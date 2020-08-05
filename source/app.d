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
    this.args = args;
    this.execute = execute;
  }
}

Type String;
Type Identifier;
Type I32;
Type F32;
static this () {
  String = Type (`String`);
  Identifier = Type (`Identifier`);
  auto I32 = Type (`I32`);
  auto F32 = Type (`F32`);
}
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

string unescape (string toUnescape) {
  stderr.writeln (`Note: unescape not implemented`);
  return toUnescape;
}

void main () {
  import parser;
  auto asValueList (string line, IdentifierScope [] identifierScopes) {
    auto tokens = lex (line);
    writeln (`Got as tokens `, tokens);
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
            auto unescaped = strVal.unescape;
            bool foundRef = false;
            foreach_reverse (idScope; identifierScopes) {
              auto referenced = unescaped in idScope.vals;
              if (referenced != null) {
                foundRef = true;
                toRet ~= *referenced;
                break;
              }
            }
            if (!foundRef) {
              toRet ~= Value (
                Identifier, Variant (unescaped)
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

  ValueOrErr processLine (
    string line
    , IdentifierScope [] identifierScopes
    , RuleScope [] ruleScopes
  ) {
    auto asVals = asValueList (line, identifierScopes);
    writeln (`Got as value list `, asVals);
    foreach_reverse (rules; ruleScopes) {
      auto tried = rules.execute (asVals);
      if (!tried.isNull ()) {
        return tried;
      }
    }
    return ValueOrErr ();
  }

  ValueOrErr processLines (
    string [] lines
    , IdentifierScope [] identifierScopes
    , RuleScope [] ruleScopes
  ) {
    auto lastIdScope = IdentifierScope ();
    foreach (line; lines) {
      auto returned = processLine (line, identifierScopes ~ lastIdScope, ruleScopes);
      if (returned.isNull ()) {
        stderr.writeln (`Line `, line, ` errored :O`);
        return returned;
      } else {
        lastIdScope = IdentifierScope (["_" : returned.get ()]);
      }
    }
    return ValueOrErr (lastIdScope.vals ["_"]);
  }

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
  processLines (
    [
      `5 plus 4`
    ], [
    ], [
      globalRules
    ]
  ).writeln;
  /+
  auto TypeT = Type (`Type`);
  auto Enum = CompositeType (2, `Enum`);
  auto exampleStruct = ["strField" : String, "intField" : I32];
  auto NameType = Enum.instance ([String, TypeT]);
  auto ExampleStruct = Type (`ExampleStruct`);
  auto construct = Rule (
    [TypeOrString ("construct"), TypeOrString (NameType)]
    , (Value [] args){
      auto namedArgs = args [1].value;
      return ValueOrErr (Value (ExampleStruct, namedArgs));
    }
  );
  auto strLiteral = Value (String, Variant ("Example string"));
  auto intLiteral = Value (I32, Variant (34));
  auto inputArg = Value (NameType, Variant (
    [
      Value (String, Variant ("strField")) : strLiteral
      , Value (String, Variant ("intField")) : intLiteral
    ]
  ));
  globalScope.execute (
    [Value (String, Variant ("construct")), inputArg]
  ).writeln;
  +/
}
