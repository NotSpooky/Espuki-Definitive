module app;

import std.stdio;
import std.variant;
import std.algorithm;
import std.range;
import std.conv : to, text;
import std.typecons;

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

alias TypeOrString = Algebraic!(Type, string);
alias ValueOrErr = Nullable!Value;
alias ApplyFun = ValueOrErr delegate (Value [] apply);
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

import intrinsics;
struct RuleScope {
  @disable this ();
  Rule [] rules;
  this (Rule [] rules) {
    this.rules = rules;
  }

  // Didn't let me use a Nullable!Value instead of pointer :(
  ValueOrErr execute (Value [] args, bool usedUnderscore, Value * underscoreVal) {
    writeln (`Executing `, args, `. Used _? `, usedUnderscore);
    auto validMatches = rules.filter! ((rule) {
      if (usedUnderscore) {
        // Args should appear in the same order as the rule
        if (rule.args.length != args.length) return false;
        return args.zip (rule.args).all! ((pair) {
          auto arg = pair [0];
          auto ruleArg = pair [1];
          writeln (`Rule arg is `, ruleArg);
          if (ruleArg.type == typeid (string)) {
            // In case of strings, make sure the value has the same string
            return arg.type == Identifier && arg.value.get!string == ruleArg.get!string;
          } else {
            assert (ruleArg.type == typeid (Type));
            return arg.type == ruleArg.get!Type;
          }
        });
      } else {
        // First non-string arg is automatically inserted from _
        if (rule.args.length != args.length + 1) return false;
        bool alreadyPlacedImplicitUnderscore = false;
        auto argsCopy = args.save;
        foreach (i, ruleArg; rule.args) {
          writeln (`Rule arg is `, ruleArg);
          if (ruleArg.type == typeid (string)) {
            auto arg = argsCopy.front;
            writeln (`1. `, arg.value, ` <-> `, ruleArg);
            // In case of strings, make sure the value has the same string
            if (!(arg.type == Identifier && arg.value.get!string == ruleArg.get!string)) {
              // Text differs
              return false;
            }
          } else if (alreadyPlacedImplicitUnderscore) {
            auto arg = argsCopy.front;
            writeln (`2. `, arg.value, ` <-> `, ruleArg);
            // A value argument.
            assert (ruleArg.type == typeid (Type));
            if (arg.type != ruleArg.get!Type) {
              return false;
            }
          } else {
            writeln (alreadyPlacedImplicitUnderscore);
            alreadyPlacedImplicitUnderscore = true;
            writeln (alreadyPlacedImplicitUnderscore);
            // A value argument. We will insert the value that the underscore points to.
            assert (underscoreVal != null);
            writeln (`3. `, *underscoreVal, ` <-> `, ruleArg);
            writeln (underscoreVal.type, ` |-| `, ruleArg.get!Type);
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
    writeln (`Got as args to send: `, args);
    return validMatches [0].execute (args);
  }
}

struct Value {
  Type type;
  Variant value;
  this (Type type, Variant value) {
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

struct IdentifierScope {
  Value [string] vals;
}

import parser;
auto asValueList (Token [] tokens, IdentifierScope [] identifierScopes) {
  Appender! (Value []) toRet;
  bool usedUnderscore = false;
  with (Token.Type) {
    for (; !tokens.empty; tokens.popFront ()) {
      auto token = tokens.front ();
      auto strVal = token.strVal;
      switch (token.type) {
      /+
      , openingBracket
      , closingBracket
      , openingParenthesis
      , closingParenthesis
      , openingSquareBracket
      , closingSquareBracket
      , stringLiteral
      , singleQuotSymbol
      +/
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
        default:
          assert (0, `TODO: Parse ` ~ token.to!string);
      }
    }
  }
  return tuple! (`values`, `usedUnderscore`) (toRet.data, usedUnderscore);
}

alias TokenListR = Nullable! (Token [][]);

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
    auto asVals = asValueList (tokenLine, identifierScopes ~ lastIdScope);
    writeln (`Got as value list `, asVals.values, ` used _? `, asVals.usedUnderscore);
    bool foundRule = false;
    foreach_reverse (rules; ruleScopes) {
      auto underscoreVal = `_` in lastIdScope.vals;
      /+
      ValueOrErr underscoreValAsNullable;
      if (underscoreVal != null) {
        underscoreValAsNullable = * underscoreVal;
      }+/
      auto tried = rules.execute (
        asVals.values
        , asVals.usedUnderscore || i == 0 // First line can't use underscore
        , underscoreVal
      );
      if (!tried.isNull ()) {
        lastIdScope = IdentifierScope (["_" : tried.get ()]);
        writeln (`lastIdScope is `, lastIdScope);
        foundRule = true;
        break;
      } 
    }
    if (!foundRule) {
      stderr.writeln (`No rule found :(`);
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
}
