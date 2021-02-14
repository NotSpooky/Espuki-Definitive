module intrinsics;

import std.algorithm;
import std.conv;
import std.range;
import execute;
import parser : Expression;
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
TypeId TupleT;
TypeId NamedTypeT;
TypeId ExpressionT;
TypeId RuleT;
ParametrizedKind Array;
ParametrizedKind SumType;
ParametrizedKind Struct;
TypeId EmptyArray; // Not an instance of array, has special rules.
TypeId ArrayOfTypes;
// Note: To prevent forward refs, this uses void * (which is an Expression [] *)
TypeId ArrayOfExpressions;

RuleScope * globalRules;
/// In text code it's just an stack, in a graph it changes, however.
ValueScope globalScope;

RTValue asSymbol (string name) {
  return RTValue (Symbol, Var (name));
}
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

/// Includes itself and all the types this one can implicitly convert to.
auto visitTypeConvs (TypeId type) {
  auto tInImplicit = type in implicitConversions;
  if (tInImplicit) {
    return (*tInImplicit).visitT (type);
  }
  return [type];
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
  TupleT = addPrimitive (`Tuple`);
  NamedTypeT = addPrimitive (`NamedType`);
  ExpressionT = addPrimitive (`Expression`);
  RuleT = addPrimitive (`Rule`);
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

  import std.functional : toDelegate;
  globalRules = new RuleScope ([
    // I32 plus I32
    fromD!plus (automaticParams!plus (1, `+`))
    , fromD!writeString (automaticParams!writeString (0, `writeln`))
    // apply Expression [].
    , Rule (
      [
        RuleParam (I32)
        , RuleParam (`apply`.asSymbol ())
        , RuleParam (ArrayOfExpressions)
      ]
      , (
        in RTValue [] args
        , ref RuleMatcher ruleMatcher
        , ref ValueScope valueScope
      ) {
        assert (args.length == 3);
        /+debug writeln (
          "Apply called, will now execute with:\n\t"
          , args [0].value, ` in `, args [1].value
        );+/
        auto result = executeFromExpressions (
          args [2].value.get! (Expressions).expressions
          , [args [0]]
          , ruleMatcher
          , globalScope
        );
        if (result.isNull) {
          throw new Exception (`Got no result from apply`);
        }
        //debug writeln (`Apply result: `, result);
        return result.get!RTValue;
      }.toDelegate
    )
    // Tuple 'at' index
    , Rule (
      [
        RuleParam (TupleT)
        , RuleParam (`at`.asSymbol)
        , RuleParam (I32)
      ]
      , (
        in RTValue [] args
        , ref RuleMatcher ruleMatcher
        , ref ValueScope valueScope
      ) {
        assert (args.length == 3);
        // Cannot return the indexed directly, as it's const.
        auto source = args [0].value.get!(RTValue [])[args [2].value.get!(int)];
        return RTValue (source.type, source.value);
      }
    )
    // NamedValueT constructor.
    , Rule (
      [
        RuleParam (Kind)
        , RuleParam (Symbol)
      ]
      , (
        in RTValue [] args
        , ref RuleMatcher ruleMatcher
        , ref ValueScope valueScope
      ) {
        assert (args.length == 2);
        return RTValue (NamedTypeT, Var (NamedType (
          args [1].value.get!string, args [0].value.get!TypeId
        )));
      }
    )
    // Rule to add more rules.
    , Rule (
      [
        RuleParam (TupleT)
        , RuleParam (ArrayOfExpressions)
      ]
      , (
        in RTValue [] args
        , ref RuleMatcher ruleMatcher
        , ref ValueScope valueScope
      ) {
        assert (args.length == 2);
        // debug writeln (`Adding rule with params `, args [0]);
        struct NameWithPos {
          string name;
          size_t pos;
        }
        NameWithPos [] namedArgLocations;
        RuleParam [] rParams;
        foreach (i, rParam; args [0].value.get! (RTValue [])) {
          // TODO: Add a way to escape named types so they can be found by value.
          if (rParam.type == NamedTypeT) {
            auto asNT = rParam.value.get!NamedType;
            rParams ~= RuleParam (asNT.type);
            namedArgLocations ~= NameWithPos (asNT.name, i);
          } else {
            rParams ~= RuleParam (rParam);
          }
        }
        auto toRet = new Rule (
          rParams
          , (
            in RTValue [] newRArgs
            , ref RuleMatcher ruleMatcher
            , ref ValueScope valueScope
          ) {
            RTValue [string] newScope;
            foreach (namedArg; namedArgLocations) {
              newScope [namedArg.name] = newRArgs [namedArg.pos];
            }
            return valueScope.withScope! ((s) {
              auto result = executeFromExpressions (
                args [1].value.get! (Expressions).expressions
                , []
                , ruleMatcher
                , s
              );
              if (result.isNull) {
                throw new Exception (`Got no result`);
              }
              return result.get!RTValue;
            }) (newScope);
          }
        );
        ruleMatcher.addRule (toRet);
        return RTValue (RuleT, Var (toRet));
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
  } else static if (is (DType == RTValue [])) {
    alias TypeMapping = TupleT;
  }
}

import std.traits;
import rulematcher;
RuleParam [] automaticParams (alias Fun)(
  size_t nameLocation = 0
  , string name = Fun.mangleof
) {
  alias DParams = Parameters!Fun;
  RuleParam [] params;
  foreach (Param; DParams) {
    params ~= RuleParam (TypeMapping!Param);
  }
  return params [0 .. nameLocation]
    ~ RuleParam (RTValue (Symbol, Var (name)))
    ~ params [nameLocation .. $];
}

import std.conv : to, text;
Rule fromD (alias Fun) (RuleParam [] params = automaticParams!Fun) {
  alias RetType = ReturnType!Fun;
  alias Params = Parameters!Fun;
  return Rule (params, (
    in RTValue [] args
    , ref RuleMatcher ruleMatcher
    , ref ValueScope valueScope
  ) {
      uint lastIdx = 0;
      // TODO: Foreach with mixin that sets all the values from args.
      static foreach (i, Param; Params) {
        while (args [lastIdx].type == Symbol) {
          lastIdx ++;
        }
        /+
        auto expectedType = TypeMapping!Param;
        assert (
          args [i].type == expectedType
          , text (`Expected arg `, i, ` of `, FunName, ` to be of type `, expectedType.name)
        );
        +/
        mixin (q{auto arg} ~ i.to!string ~ q{ = args [lastIdx].value.get!Param ();});
        lastIdx ++;
      }
      mixin (
        q{auto result = Fun (}
          ~ iota (Params.length)
          .map!(`"arg" ~ a.to!string`)
          .joiner (`, `)
          .to!string 
        ~ q{);}
      );
      return RTValue (TypeMapping!RetType, Var (result));
    }
  );
}
