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
      in RTValue [] args
      , ref RuleTree ruleTree
    ) {
      debug import std.stdio;
      debug writeln (`Identity args `, args);
      assert (args.length == 1);
      return RTValueOrErr (args [0]);
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
    , fromD!plus (automaticParams!plus (1))
    , fromD!writeString (automaticParams!writeString (0, `writeln`))
    , Rule (
      [TypeOrSymbol (I32), TypeOrSymbol (`apply`), TypeOrSymbol (Function)], (
        in RTValue [] args
        , ref RuleTree ruleTree
      ) {
        import std.stdio;
        assert (args.length == 2);
        /*debug writeln (
          "Apply called, will now execute with:\n\t"
          , args [0].value, ` in `, args [1].value
        );*/
        import parser : Expression;
        auto result = executeFromExpressions (
          args [1].value.get! (Expression [])
          , [args [0]]
          , ruleTree
        );
        // debug writeln (`Apply result: `, result);
        return result;
      }
    )
  ]);
}

extern (C) {
  int plus (int a, int b) { return a + b; }
  string writeString (string toWrite) {
    import std.stdio;
    writeln (toWrite);
    return toWrite;
  }
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

import std.traits;
TypeOrSymbol [] automaticParams (alias Fun)(
  size_t nameLocation = 0
  , string name = Fun.mangleof
) {
  alias DParams = Parameters!Fun;
  TypeOrSymbol [] params;
  foreach (Param; DParams) {
    params ~= TypeOrSymbol (TypeMapping!Param);
  }
  return params [0 .. nameLocation]
    ~ TypeOrSymbol (name)
    ~ params [nameLocation .. $];
}

import std.conv : to, text;
Rule fromD (alias Fun) (TypeOrSymbol [] params = automaticParams!Fun) {
  alias RetType = ReturnType!Fun;
  alias Params = Parameters!Fun;
  return Rule (params, (
    in RTValue [] args
    , ref RuleTree ruleTree
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
      return RTValueOrErr (RTValue (TypeMapping!RetType, Var (result)));
    }
  );
}
