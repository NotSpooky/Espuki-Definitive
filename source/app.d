module app;

import std.stdio;
import std.variant;
import std.algorithm;
import std.range;
import std.conv : to, text;
import std.typecons : Nullable, nullable;

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

  ValueOrErr execute (Value [] args) {
    auto validMatches = rules.filter!((rule) {
      if (rule.args.length != args.length) return false;
      return args.zip (rule.args).all!((pair) {
        auto arg = pair [0];
        auto ruleArg = pair [1];
        if (ruleArg.type == typeid (string)) {
          // In case of strings, make sure the value has the same string
          return arg.type == Identifier && arg.value.get!string == ruleArg.get!string;
        } else {
          assert (ruleArg.type == typeid (Type));
          return arg.type == ruleArg.get!Type;
        }
      });
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
  return toRet.data;
}

alias TokenListR = Nullable! (Token [][]);
TokenListR getTokens (R)(
  R lines
  , bool inAsteriskComment
  , uint plusCommentDepth
) {
  Appender!(Token [][]) currentLineTokens;
  for (; !lines.empty; lines.popFront) {
    auto line = lines.front;
    writeln (`Lexing line `, line);
    auto lexed = lex (line, inAsteriskComment, plusCommentDepth);
    inAsteriskComment = lexed.inAsteriskComment;
    plusCommentDepth = lexed.plusCommentDepth;
    auto tokens = lexed.tokens;
    // Ignore empty lines.
    if (tokens.empty) {
      lines.popFront ();
      continue;
    }
    // Lines ending with backslash are concatenated to the next one
    if (tokens [$-1].type == Token.Type.backslash) {
      lines.popFront ();
      auto following = getTokens (lines, inAsteriskComment, plusCommentDepth);
      if (following.empty) {
        stderr.writeln (`Expected another line after '\'`);
        return Nullable! (Token [][]) ();
      } else if (following.isNull ()) {
        return following;
      } else {
        return TokenListR (
          currentLineTokens.data
            ~ [tokens [0..$-1] ~ following [0]]
            ~ following [1..$]
        );
      }
    } else {
      currentLineTokens ~= tokens;
    }
  }
  writeln (`Finished getTokens`);
  return TokenListR (currentLineTokens.data);
}

ValueOrErr processLines (R)(
  R lines
  , IdentifierScope [] identifierScopes
  , RuleScope [] ruleScopes
) {
  auto lastIdScope = IdentifierScope ();
  auto tokenLineRange = getTokens (lines, false, 0);
  if (tokenLineRange.isNull ()) {
    stderr.writeln (`Error getting tokens :( `);
    return ValueOrErr ();
  }

  writeln (`Got tokens : `, tokenLineRange);
  foreach (tokenLine; tokenLineRange.get ()) {
    auto asVals = asValueList (tokenLine, identifierScopes);
    writeln (`Got as value list `, asVals);
    bool foundRule = false;
    foreach_reverse (rules; ruleScopes) {
      auto tried = rules.execute (asVals);
      if (!tried.isNull ()) {
        lastIdScope = IdentifierScope (["_" : tried.get ()]);
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
  /+
  auto globalRules = RuleScope ([
    Rule (
      // Single int returns itself
      [TypeOrString (I32)], (Value [] args) {
        writeln (`First rule, got args `, args);
        assert (args.length == 1);
        return ValueOrErr (args [0]);
      }
    ), Rule (
      // Example addition
      [TypeOrString (I32), TypeOrString (`plus`), TypeOrString (I32)], (Value [] args) {
        writeln (`Second rule, got args `, args);
        assert (args.length == 3);
        return ValueOrErr (
          Value (I32, Variant (args [0].value.get!int () + args [2].value.get!int ()))
        );
      }
    )
  ]);
  +/
  assert (globalRules != null);
  processLines (
    File (`example.es`).byLineCopy()
    , [
    ], [
      * globalRules
    ]
  ).writeln;
}
