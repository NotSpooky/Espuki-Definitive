module value;

import std.sumtype;
import std.conv : to;
import rule;
import type;
debug import std.stdio;

struct StructType {
  size_t [TypeId] offsets;
}

struct Expression {
  // TODO
  int a; // TODO: remove
}

alias Var = SumType! (
  bool
  , float
  , string
  , int
  , TypeId
  , NamedType
  , Rule *     // For RuleT
  , Value []   // For TupleT.
  , This []    // For arrays and structs.
  , typeof (null)
  , Expression [] * /* Was Expressions */
  , StructType
  , EspukiAA
);

// To prevent toHash errors.
struct VarWrapper {
  Var var;
  size_t toHash () const nothrow {
    return var.match! (a => a.hashOf ());
  }
  this (Var val) {
    this.var = val;
  }
  this (T)(in T val) if (!is (T == Var)) {
    this.var = Var (val);
  }
}

struct EspukiAA {
  Var [VarWrapper] val;
}

// Note: Verbose name because TypeId == long.
Value typeToValue (TypeId type) {
  return Value (Kind, Var (type));
}

// Compiled values aren't known in the interpreter, they are meant to be calculated
// at runtime.
struct CompiledValue {
  Value [] dependencies;
  void toString (
    scope void delegate (const (char)[]) sink
  ) const {
    sink(`Compiled TODO: Add rule and dependencies`);
  }
}

alias ValueContent = SumType! (VarWrapper, CompiledValue);

struct Value {
  TypeId type;
  ValueContent value;
  
  this (TypeId type, Var value) {
    this.type = type;
    this.value = ValueContent (VarWrapper (value));
  }
  @disable this ();

  size_t toHash () const nothrow {
    try {
      return type.hashOf () + this.extractVar ()
        .match! (a => a.hashOf ());
    } catch (Exception ex) {
      assert (0, ex.message);
    }
  }

  bool opEquals (inout ref Value other) const 
  out (res) {
    // writeln (`Which yields `, res);
  } do {
    debug {
      //writeln (`Comparing `, this.to!string, ` to `, other.to!string);
    }
    return this.type == other.type && this.extractVar () == other.extractVar ();
  }

  // Use only if the value is interpreted.
  Var extractVar () inout {
    return this.value.tryMatch! ((VarWrapper v) => v.var);
  }

  private string valueToString (TypeId elementType, Var var) const {
      return Value (elementType, var).to!string;
  }

  void toString (
    scope void delegate (const (char)[]) sink
  ) const {
    import t = type;
    import std.algorithm;
    value.match! (
      (VarWrapper interpretedVal) {
        sink (globalTypeInfo [this.type].name);
        sink (` `);
        interpretedVal.var.match! (
          (const Var [] v) {
            if (isParametrizedFrom (type, MappingKind)) {
              sink (v [0].to!string);
              sink (` -> `);
              sink (v [1].to!string);
            } else {
              sink (`[`);
              TypeId elementType = Any;
              if (isParametrizedFrom (type, ArrayKind)) {
                elementType = arrayElementType (type);
              }
              sink (
                v
                  .map! (b => valueToString (elementType, b))
                  .joiner (`, `)
                  .to!string
              );
              sink (`]`);
            }
          }, (string v) {
            sink (v);
          }, (const Value [] v) {
            sink (`[`);
            sink (
              v
                .map! (b => b.to!string ())
                .joiner (`, `)
                .to!string
            );
            sink (`]`);
          }, (size_t v) {
            if (type == Kind) {
              sink (globalTypeInfo [v].name);
            } else {
              sink (v.to!string);
            }
          }, (EspukiAA aa) {
            sink (`[`);
            /+sink (
              aa
                .val
                //.byKey
                .map! (pair => pair.key.to!string ~ ` to ` ~ pair.value.to!string)
                //.joiner (`, `)
                .to!string
            );+/
            sink (`... values ...`);
            sink (`]`);
          }, (v) {
            sink (v.to!string);
          }
        );
      }, (cVal) {
        sink (cVal.to!string);
      }
    );
  }
}

Value asSymbol (string symbol) {
  return Value (Symbol, Var (symbol));
}

struct Mapping {
  Value source;
  Value destination;
}

Value toEspuki (Mapping mapping) {
  auto outType = mapping.source.type.MappingTo (mapping.destination.type);
  return Value (
    outType, Var ([mapping.source.extractVar (), mapping.destination.extractVar ()])
  );
}

Value toEspuki (EspukiAA aa, TypeId keyType, TypeId valueType) {
  return Value (associativeArrayOf (keyType, valueType), Var (aa));
}
