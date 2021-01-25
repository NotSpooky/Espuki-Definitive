module app;

import std.stdio;
import execute;
import lexer : lex;

void main () {
  import std.algorithm;
  import std.conv : to;
  import mir.algebraic : visit;
  import intrinsics :globalTypes;
  lex (File (`example.es`).byLineCopy (), globalTypes).visit! (
    (UserError ue) => writeln (`Error: `, ue.message)
    , (expressions) => writeln (expressions)
  );
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
