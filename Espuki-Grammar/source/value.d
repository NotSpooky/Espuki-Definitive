import std.sumtype;
import std.conv : to;
import rule;
import type : TypeId, NamedType, globalTypeInfo;

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
);

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

// To prevent toHash warnings.
struct VarWrapper {
  Var var;
  size_t toHash () const nothrow @safe {
    return var.match! (a => a.hashOf ());
  }
}

struct Value {
  TypeId type;
  SumType! (VarWrapper, CompiledValue) value;
  
  this (TypeId type, Var value) {
    this.type = type;
    this.value = SumType! (VarWrapper, CompiledValue) (VarWrapper (value));
  }

  size_t toHash () const nothrow @safe {
    return type.hashOf () + value.match! (a => a.toHash(), a => a.hashOf ());
  }

  void toString (
    scope void delegate (const (char)[]) sink
  ) const {
    import std.algorithm;
    value.match! (
      (VarWrapper interpretedVal) {
        sink (globalTypeInfo [this.type].toString ());
        sink (` `);
        interpretedVal.var.match! (
          (Var [] v) {
            sink (`[`);
            sink (
              v
                .map! (b => b.to!string ())
                .joiner (`, `)
                .to!string
            );
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
