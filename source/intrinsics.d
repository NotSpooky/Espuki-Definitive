module intrinsics;

import std.algorithm;
import std.conv;
import std.range;
import execute;
debug import std.stdio;

TypeId Kind; // Just a Type of Type.
TypeId String;
TypeId Symbol;
TypeId I8;
TypeId I16;
TypeId I32;
TypeId I64;
TypeId F32;
TypeId F64;
TypeId NamedTypeT;
TypeId ExpressionT;
ParametrizedKind Array;
ParametrizedKind SumType;
ParametrizedKind Struct;
TypeId EmptyArray; // Not an instance of array, has special rules.
TypeId ArrayOfTypes;
// Note: To prevent forward refs, this uses void * (which is an Expression [] *)
TypeId ArrayOfExpressions;

RuleScope * globalRules;
ValueScope globalScope;

struct TypeImplicitConversions {
  TypeId [] moreGeneral;

  private auto visitT (TypeId type) const {
    bool [TypeId] visitedTypes;
    auto typesToTry = [type];
    Appender! (TypeId []) toRet;
    while (!typesToTry.empty) {
      const t = typesToTry [$-1];
      typesToTry = typesToTry [0 .. $-1];
      toRet ~= t;
      const tInImplicit = t in implicitConversions;
      if (tInImplicit) {
        foreach (generalType; (* tInImplicit).moreGeneral) {
          visitedTypes.require (generalType, {
            typesToTry ~= generalType;
            return true;
          } ());
        }
      }
    }
    return toRet [];
  }
}

TypeImplicitConversions [TypeId] implicitConversions;

auto visitTypeConvs (TypeId type) {
  auto tInImplicit = type in implicitConversions;
  if (tInImplicit) {
    return (*tInImplicit).visitT (type);
  }
  return TypeId [].init;
}

private TypeId addPrimitive (string name) {
  // As of now, all variables will be stored on a Var, so that'll be the size.
  return globalScope.addType (name, Var.sizeof).get!TypeId;
}

shared static this () {
  // Primitives:
  Kind = addPrimitive (`Kind`);
  String = addPrimitive (`String`);
  Symbol = addPrimitive (`Symbol`);
  I8 = addPrimitive (`I8`);
  I16 = addPrimitive (`I16`);
  I32 = addPrimitive (`I32`);
  I64 = addPrimitive (`I64`);
  F32 = addPrimitive (`F32`);
  F64 = addPrimitive (`F64`);
  NamedTypeT = addPrimitive (`NamedType`);
  ExpressionT = addPrimitive (`Expression`);
  EmptyArray = addPrimitive (`EmptyArray`);

  // Implicit conversions:
  implicitConversions [F32] = TypeImplicitConversions ([F64]);
  implicitConversions [I32] = TypeImplicitConversions ([F64, I64]);
  implicitConversions [I16] = TypeImplicitConversions ([F32, I32]);
  implicitConversions [I8] = TypeImplicitConversions ([I16]);

  // Parametrized types:
  Array = ParametrizedKind (
    `Array`, [Kind]
  );
  ArrayOfTypes = arrayOf (Kind);
  // Array of types should be here too?
  SumType = ParametrizedKind (
    `SumType`, [ArrayOfTypes]
  );
  Struct = ParametrizedKind (
    `Struct`, [ArrayOfTypes]
  );
  auto SymbolOrNamedType = sumTypeOf (
    [typeToRTValue (Symbol), typeToRTValue (NamedTypeT)]
  );
  auto ArrayOfSymbolOrNamedType = arrayOf (SymbolOrNamedType);
  ArrayOfExpressions = arrayOf (ExpressionT);

  globalRules = new RuleScope ([
    // I32 plus I32
    fromD!plus (automaticParams!plus (1))
    , fromD!writeString (automaticParams!writeString (0, `writeln`))
    , Rule ( // apply Expression []
      [
        TypeOrSymbol (I32)
        , TypeOrSymbol (`apply`)
        , TypeOrSymbol (ArrayOfExpressions)]
      , (
        in RTValue [] args
        , ref RuleTree ruleTree
      ) {
        assert (args.length == 2);
        /+debug writeln (
          "Apply called, will now execute with:\n\t"
          , args [0].value, ` in `, args [1].value
        );+/
        import parser : Expression;
        auto result = executeFromExpressions (
          args [1].value.get! (Expressions).expressions
          , [args [0]]
          , ruleTree
          , globalScope
        );
        //debug writeln (`Apply result: `, result);
        return result;
      }
    )
    , Rule ( // Symbol | NamedType [] Expression [] // TODO: Change to new syntax
      [TypeOrSymbol (ArrayOfSymbolOrNamedType), TypeOrSymbol (ArrayOfExpressions)]
      , (
        in RTValue [] args
        , ref RuleTree ruleTree
      ) {
        assert (args.length == 2);
        debug writeln (`TODO: Declare a function. Called with `, args);
        return RTValueOrErr (UserError (`TODO: Declare a function`));
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
      mixin (
        q{auto result = Fun (}
          ~ iota (Params.length)
          .map!(`"arg" ~ a.to!string`)
          .joiner (`, `)
          .to!string 
        ~ q{);}
      );
      return RTValueOrErr (RTValue (TypeMapping!RetType, Var (result)));
    }
  );
}
