module intrinsics;

import execute;

Type String;
Type Identifier;
Type I32;
Type F32;
Type Function;

RuleScope * globalRules;
TypeScope globalTypes;

Rule identity (Type type) {
  return Rule (
    // Single int returns itself
    [TypeOrSymbol (type)], (
      RTValue [] args
      , RuleScope [] scopes
      , bool usedUnderscore
    ) {
      assert (args.length == 1);
      return ValueOrErr (args [0]);
    }
  );
}
static this () {
  String = globalTypes.add (`String`).get!Type;
  Identifier = globalTypes.add (`Identifier`).get!Type;
  I32 = globalTypes.add (`I32`).get!Type;
  F32 = globalTypes.add (`F32`).get!Type;
  Function = globalTypes.add (`Function`).get!Type;

  globalRules = new RuleScope ([
    identity (String)
    , identity (Identifier)
    , identity (I32)
    , identity (F32)
    , identity (Function)
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
    , fromD!plus
    +/
  ]);
}

/+
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
    Value [] args
    , RuleScope [] scopes
    , IdentifierScope lastIdScope
    , bool usedUnderscore
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
        mixin (q{auto arg} ~ i.to!string ~ q{ = args [i + 1].value.get!Param ();});
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
      return ValueOrErr (mixin (q{Value (TypeMapping!RetType, Variant(result))}));
    }
  );
}
+/
