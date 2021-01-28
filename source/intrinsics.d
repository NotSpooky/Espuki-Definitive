module intrinsics;

import std.algorithm;
import std.conv;
import execute;

Type Kind; // Just a Type of Type.
Type String;
Type Symbol;
Type I32;
Type F32;
Type Function;

RuleScope * globalRules;
TypeScope globalTypes;

Rule identity (Type [] types) {
  return Rule (
    // Single Type instanceOfType returns itself
    [TypeOrSymbol (Kind)]
    , (
      RTValue [] args
      , in RuleTree ruleTree
    ) {
      debug import std.stdio;
      debug writeln (`Identity args `, args);
      assert (args.length == 1);
      return ValueOrErr (args [0]);
    }
  );
}

Type [Type []] sumTypeInstances;
Rule [] instanceSumType (Type [] types) {
  auto existing = types in sumTypeInstances;
  Type sumType = existing
    ? (*existing) : Type (types.map!`a.name`.joiner (` |`).to!string);
  debug import std.stdio;
  debug writeln (`TODO: Implement pattern matching so that I can match the type at the beginning`);
  return [];
}

static this () {
  Kind = globalTypes.add (`Kind`).get!Type;
  String = globalTypes.add (`String`).get!Type;
  Symbol = globalTypes.add (`Symbol`).get!Type;
  I32 = globalTypes.add (`I32`).get!Type;
  F32 = globalTypes.add (`F32`).get!Type;
  Function = globalTypes.add (`Function`).get!Type;

  globalRules = new RuleScope ([
    identity ([Kind, String, Symbol, I32, F32, Function])
    , fromD!plus
    /+
    , Rule (
      [TypeOrSymbol (`apply`), TypeOrSymbol (I32), TypeOrSymbol (Function)], (
        RTValue [] args
        , RuleScope [] scopes
        , bool usedUnderscore
      ) {
        import std.stdio;
        assert (args.length == 3);
        writeln (
          "Apply called, will now execute with:\n\t"
          , args [2].value, /+"\n\t", scopes,+/ "\n\t", lastIdScope, "\n\t> Used underscore? ", usedUnderscore
        );
        auto returned = executeFromValues (
          args [2].value.get!AsValueListRet
          , scopes
          , lastIdScope
          , usedUnderscore
        );
        if (returned.isNull ()) {
          return ValueOrErr ();
        } else {
          return ValueOrErr (lastIdScope.vals [`_`]);
        }
      }
    )
    +/
  ]);
}

extern (C) {
  int plus (int a, int b) { return a + b; }
}

template TypeMapping (DType) {
  static if (is (DType == string)) {
    alias TypeMapping = String;
  } else static if (is (DType == int)) {
    alias TypeMapping = I32;
  } else static if (is (DType == float)) {
    alias TypeMapping = F32;
  } else static if (is (DType == AsValueListRet)) {
    alias TypeMapping = Function;
  }
}

import std.conv : to, text;
Rule fromD (alias Fun) () {
  import std.traits;
  alias RetType = ReturnType!Fun;
  alias Params = Parameters!Fun;
  enum FunName = Fun.mangleof;
  TypeOrSymbol [] params = [TypeOrSymbol (FunName)];
  foreach (Param; Params) {
    params ~= TypeOrSymbol (TypeMapping!Param);
  }
  return Rule (params, (
    RTValue [] args
    , in RuleTree ruleTree
  ) {
      import std.stdio;
      // TODO: Foreach with mixin that sets all the values from args.
      static foreach (i, Param; Params) {
        /+
        auto expectedType = TypeMapping!Param;
        assert (
          args [i].type == expectedType
          , text (`Expected arg `, i, ` of `, FunName, ` to be of type `, expectedType.name)
        );
        +/
        mixin (q{auto arg} ~ i.to!string ~ q{ = args [i].value.get!Param ();});
      }
      import std.range;
      import std.algorithm;
      mixin (
        q{auto result = Fun (}
          ~ iota (Params.length)
          .map!(`"arg" ~ a.to!string`)
          .joiner (`, `)
          .to!string 
        ~ q{);}
      );
      import std.variant;
      return ValueOrErr (RTValue (TypeMapping!RetType, Var (result)));
    }
  );
}
