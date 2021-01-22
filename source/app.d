module app;

import std.stdio;
import mir.algebraic;
import lexer;
void main () {
  asExpressions (File (`example.es`).byLineCopy ()).visit! (
    (Expression [] expressions) { 
      foreach (expression; expressions) {
        debug expression.writeln ();
      }
    }
    , (UserError ue) { stderr.writeln (`Error: `, ue.message); }
  );
}

private uint lastTypeId;
struct Type {
  //@disable this (); // Cannot disable when assigning to Variant :(
  uint id;
  string name; // Just for pretty printing.
  this (string name) {
    this.name = name;
    this.id = lastTypeId;
    lastTypeId ++;
  }
  bool opEquals()(auto ref const Type other) const {
    return other.id == this.id;
  }
}

alias Var = Variant! (float, string, int);
/// A value in the interpreter.
struct RTValue {
  Type type;
  Var value;
  this (Type type, Var value) {
    this.type = type;
    this.value = value;
  }
  void toString (
    scope void delegate (const (char)[]) sink
  ) {
    sink (type.name);
    sink (` `);
    sink (value.toString ());
  }
}

alias ValueOrErr = Nullable!RTValue;
alias ApplyFun = ValueOrErr delegate (
  RTValue [] apply
  , RuleScope [] scopes
  , bool usedUnderscore
);

alias TypeOrString = Variant! (Type, string);
struct Rule {
  @disable this ();
  TypeOrString [] args;
  // Can assume that execute has correct arg types.
  ApplyFun execute;
  this (TypeOrString [] args, ApplyFun execute) {
    assert (args.length > 0, `Rule with no args`);
    this.args = args;
    this.execute = execute;
  }
}

/// An error in the code that the compiler/interpreter should show.
struct UserError {
  string message;
}

import intrinsics;
struct RuleScope {
  @disable this ();
  Rule [] rules;
  this (Rule [] rules) {
    this.rules = rules;
  }

  /+
  // Didn't let me use a Nullable!Value instead of pointer :(
  ValueOrErr execute (
    AsValueListRet valListWithUnderscore
    , RuleScope [] scopes
    , IdentifierScope lastIdScope
    , bool inferUnderscore
    , Value * underscoreVal
  ) {
    auto args = valListWithUnderscore.values;
    writeln (`Executing `, valListWithUnderscore, `. Infer _? `, inferUnderscore);
    auto validMatches = rules.filter! ((rule) {
      if (inferUnderscore) {
        // First non-string arg is automatically inserted from _
        if (rule.args.length != args.length + 1) return false;
        bool alreadyPlacedImplicitUnderscore = false;
        auto argsCopy = args.save;
        foreach (i, ruleArg; rule.args) {
          if (ruleArg.type == typeid (string)) {
            auto arg = argsCopy.front;
            // In case of strings, make sure the value has the same string
            if (!(arg.type == Identifier && arg.value.get!string == ruleArg.get!string)) {
              // Text differs
              return false;
            }
          } else if (alreadyPlacedImplicitUnderscore) {
            auto arg = argsCopy.front;
            // A value argument.
            assert (ruleArg.type == typeid (Type));
            if (arg.type != ruleArg.get!Type) {
              return false;
            }
          } else {
            alreadyPlacedImplicitUnderscore = true;
            // A value argument. We will insert the value that the underscore points to.
            assert (underscoreVal != null);
            if (underscoreVal.type != ruleArg.get!Type) {
              return false;
            } else {
              args = args [0..i] ~ *underscoreVal ~ args [i..$];
              // Don't pop args as we didn't use an arg.
              continue;
            }
          }
          argsCopy.popFront ();
        }
        return true;
      } else { // Don't infer underscore.
        // Args should appear in the same order as the rule.
        if (rule.args.length != args.length) return false;
        return args.zip (rule.args).all! ((pair) {
          auto arg = pair [0];
          auto ruleArg = pair [1];
          if (ruleArg.type == typeid (string)) {
            // In case of strings, make sure the value has the same string/
            return arg.type == Identifier && arg.value.get!string == ruleArg.get!string;
          } else {
            assert (ruleArg.type == typeid (Type));
            return arg.type == ruleArg.get!Type;
          }
        });
      }
    }).array;
    if (validMatches.length == 0) {
      stderr.writeln (`No valid rule in scope level for `, args);
      return ValueOrErr ();
    } else if (validMatches.length > 1) {
      stderr.writeln (
        `Multiple matching rules for `
        , args
        , validMatches.map!`"\n\t" ~ a.to!string`.joiner ()
      );
      return ValueOrErr ();
    }
    writeln (`Got as args to execute: `, args);
    return validMatches [0].execute (
      args
      , scopes
      , lastIdScope
      , valListWithUnderscore.usedUnderscore
    );
  }
  +/
}
/+


import std.algorithm;
import std.range;
import std.conv : to, text;
import std.typecons;

string names (Type [] args) {
  return args.map!`a.name`.joiner.to!string;
}

struct CompositeType {
  uint parameterAmount;
  string name; // Just for pretty printing.
  this (uint parameterAmount, string name) {
    this.parameterAmount = parameterAmount;
    this.name = name;
  }

  auto instance (Type [] args) {
    // TODO: Can see if already instanced to avoid copies.
    assert (args.length == parameterAmount);
    return Type (this.name ~ ' ' ~ args.names);
  }
  auto curry (Type [] args) {
    // TODO: Can see if already instanced to avoid copies.
    assert (args.length <= parameterAmount);
    return CompositeType (
      (args.length - parameterAmount).to!uint
      , this.name ~ ' ' ~ args.names
    );
  }
}

struct IdentifierScope {
  Value [string] vals;
}

struct AsValueListRet {
  Value [] values;
  bool usedUnderscore;
  Nullable!string nameOfResult;
  void toString (
    scope void delegate (const (char)[]) sink
  ) {
    sink (`AVLR(`);
    sink (values.to!string);
    sink (`, used underscore? `);
    sink (usedUnderscore.to!string);
    if (!nameOfResult.isNull ()) {
      sink (`, named `);
      sink (nameOfResult.get ());
    }
    sink (`)`);
  }
}

import parser;
AsValueListRet asValueList (
  ref Token [] tokens
  , IdentifierScope [] identifierScopes
  , bool untilClosingBracket = false
) {
  Appender! (Value []) toRet;
  bool usedUnderscore = false;
  with (Token.Type) {
    for (; !tokens.empty; tokens.popFront ()) {
      auto token = tokens.front ();
      auto strVal = token.strVal;
      switch (token.type) {
      /+
      , openingParenthesis
      , closingParenthesis
      , openingSquareBracket
      , closingSquareBracket
      , stringLiteral
      , singleQuotSymbol
      +/
        case openingBracket:
          tokens.popFront ();
          auto nested = asValueList (tokens, identifierScopes, true);
          toRet ~= Value (
            Function, Variant (nested)
          );
          break;
        case closingBracket:
          if (untilClosingBracket) {
            return AsValueListRet (toRet.data, usedUnderscore, Nullable!string ());
          } else {
            throw new Exception (`Found '}' without matching '{'`);
          }
        case comma:
          throw new Exception (`Didn't expect a comma here`);
        case dot:
          throw new Exception (`Didn't expect a dot here`);
        case minus:
          tokens.popFront ();
          if (tokens.empty) {
            throw new Exception (`Didn't expect a minus at the end`);
          } else {
            auto front = tokens.front;
            auto type = front.type;
            if (type == integerLiteral) {
              toRet ~= Value (
                I32, Variant (- front.strVal.to!int)
              );
            } else if (type == floatLiteral) {
              toRet ~= Value (
                F32, Variant (- front.strVal.to!float)
              );
            } else {
              throw new Exception (
                text (`Don't know what to do with a `, type, ` after a minus`)
              );
            }
          }
          break;
        case integerLiteral:
          toRet ~= Value (
            I32, Variant (strVal.to!int)
          );
          break;
        case floatLiteral:
          toRet ~= Value (
            F32, Variant (strVal.to!float)
          );
          break;
        case identifier:
          // If there's a corresponding identifier in the scopes use that value
          // else just return the identifier for later usage (e.g. rule name matching).
          bool foundRef = false;
          foreach_reverse (idScope; identifierScopes) {
            auto referenced = strVal in idScope.vals;
            if (referenced != null) {
              foundRef = true;
              if (strVal.startsWith (`_`)) {
                usedUnderscore = true;
              }
              toRet ~= *referenced;
              break;
            }
          }
          if (!foundRef) {
            toRet ~= Value (
              Identifier, Variant (strVal)
            );
          }
          break;
        case rightArrow:
          assert (!identifierScopes.empty);
          tokens.popFront ();
          // TODO: Change to error rets.
          assert (!tokens.empty, `Unfinished line after '->'`);
          assert (
            tokens.front.type == Token.Type.identifier
            , `Expected identifier after '->'`
          );
          auto untilNow = AsValueListRet (
            toRet.data
            , usedUnderscore
            , Nullable!string (tokens.front.strVal)
          );
          tokens.popFront ();
          assert (tokens.empty, `Shouldn't have tokens after '-> identifier'`);
          return untilNow;
        default:
          assert (0, `TODO: Parse ` ~ token.to!string);
      }
    }
  }
  if (untilClosingBracket) {
    throw new Exception (`Didn't find matching '}'`);
  }
  return AsValueListRet (toRet.data, usedUnderscore, Nullable!string ());
}

alias TokenListR = Nullable! (Token [][]);
struct ReturnedAliases {
  string [] aliases;
}
alias ExecuteRet = Nullable!ReturnedAliases;
ExecuteRet executeFromValues (
  AsValueListRet valueList
  , RuleScope [] ruleScopes
  , ref IdentifierScope lastIdScope
  , bool isStartingLine
) {
  bool foundRule = false;
  auto underscoreVal = `_` in lastIdScope.vals;
  debug writeln (`> Last id scope? `, lastIdScope);
  foreach_reverse (rules; ruleScopes) {
    auto tried = rules.execute (
      valueList
      , ruleScopes
      , lastIdScope
      , (!valueList.usedUnderscore) && (!isStartingLine)
      , underscoreVal
    );
    if (!tried.isNull ()) {
      lastIdScope = IdentifierScope ([`_` : tried.get ()]);
      if (valueList.nameOfResult.isNull ()) {
        return ExecuteRet (ReturnedAliases ());
      } else {
        return ExecuteRet (ReturnedAliases ([valueList.nameOfResult.get ()]));
      }
    } 
  }
  stderr.writeln (`No rule found :(`);
  return ExecuteRet ();
}

ValueOrErr processLines (R)(
  R lines
  , IdentifierScope [] identifierScopes
  , RuleScope [] ruleScopes
) {
  auto lastIdScope = IdentifierScope ();
  auto tokenLineRange = lex (lines);
  //writeln (`Got tokens: `, tokenLineRange);
  if (tokenLineRange.isNull ()) {
    stderr.writeln (`Error getting tokens :( `);
    return ValueOrErr ();
  }

  foreach (i, tokenLine; tokenLineRange.get ()) {
    auto asVals = asValueList (tokenLine.tokens, identifierScopes ~ lastIdScope);
    writeln (`Got as value list `, asVals.values, ` used _? `, asVals.usedUnderscore);
    if (
      executeFromValues (asVals, ruleScopes, lastIdScope, tokenLine.isStart)
        .isNull ()
    ) {
      return ValueOrErr ();
    }
  }
  return ValueOrErr (lastIdScope.vals ["_"]);
}

void main () {
  assert (globalRules != null);
  processLines (
    File (`example.es`).byLineCopy()
    , [
    ], [
      * globalRules
    ]
  ).writeln;
}+/
