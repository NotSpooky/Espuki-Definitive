module intrinsics;

Type String;
Type Identifier;
Type I32;
Type F32;
Type Function;

RuleScope * globalRules;
static this () {
  String = Type (`String`);
  Identifier = Type (`Identifier`);
  I32 = Type (`I32`);
  F32 = Type (`F32`);
  Function = Type (`Function`);

  globalRules = new RuleScope ([
    identity (String)
    , identity (Identifier)
    , identity (I32)
    , identity (F32)
    , identity (Function)
    , Rule (
      [TypeOrString (`apply`), TypeOrString (I32), TypeOrString (Function)], (
        Value [] args
        , RuleScope [] scopes
        , IdentifierScope lastIdScope
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
        if (returned) {
          return ValueOrErr (lastIdScope.vals [`_`]);
        } else {
          return ValueOrErr ();
        }
      }
    )
    , fromD!plus
  ]);
  /+
  import std.stdio;
  writeln (`Made global rules: `, *globalRules);
  +/
}

extern (C) {
  int plus (int a, int b) { return a + b; }
}

import app;

Rule identity (Type type) {
  return Rule (
    // Single int returns itself
    [TypeOrString (type)], (
      Value [] args
      , RuleScope [] scopes
      , IdentifierScope lastIdScope
      , bool usedUnderscore
    ) {
      assert (args.length == 1);
      return ValueOrErr (args [0]);
    }
  );
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
  TypeOrString [] params = [TypeOrString (FunName)];
  foreach (Param; Params) {
    params ~= TypeOrString (TypeMapping!Param);
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
