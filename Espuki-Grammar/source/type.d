module type;

import std.algorithm;
import std.conv;
import std.sumtype;
import std.range;
import value;

alias TypeId = size_t;

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

/// As of now just handles type equality by id.
bool isSubTypeOf (TypeId type, TypeId parent) {
  if (type == parent) {
    return true;
  }
  return !type.visitTypeConvs.find (parent).empty;
}

struct NamedType {
  string name;
  TypeId type;
}

// Can be directly instanced for primitive types.
class TypeInfo_ {
  //const size_t size;
  string name;
  this (/*size_t size,*/ string name) {
    //this.size = size;
    this.name = name;
  }
  override string toString () {
    return name;
  }
}

private int lastTypeId = 0;
private TypeId addPrimitive (string name) {
  // As of now, all variables will be stored on a Var, so that'll be the size.
  // return globalScope.addType (name, Var.sizeof);
  import value : Var;
  globalTypeInfo ~= new TypeInfo_ (/*Var.sizeof,*/ name);
  return globalTypeInfo.length - 1;
}

// Initialized on module constructor.
TypeId Kind;   // A Type of Type.
TypeId Symbol; // A single word in the program, can be resolved as an identifier.
               // Can also be matched as-is.
TypeId String;
TypeId Bool;
TypeId I8;
TypeId I16;
TypeId I32;
TypeId I64;
TypeId F32;
TypeId F64;
TypeId TupleT;
TypeId EmptyArray;

TypeInfo_ [] globalTypeInfo;

private class ParametrizedTypeInfo : TypeInfo_ {
  const ParametrizedKind * kind;
  const Value [] args;
  this (ParametrizedKind * kind, const Value [] args /*, size_t size */) {
    assert (kind !is null);
    import std.stdio;
    string name = kind.baseName ~ ` (` ~
      args.map! (a => a.to!string)
        .joiner (`, `)
        .to!string
    ~ `)`;
    super (/*size,*/ name);
    this.kind = kind;
    this.args = args;
  }
}

/// Used to create parametrized types.
struct ParametrizedKind {
  TypeId [] argTypes;
  string baseName;
  TypeId [Value []] instances;
  this (string baseName, TypeId [] argTypes) {
    this.baseName = baseName;
    this.argTypes = argTypes;
  }

  TypeId instance (const Value [] args, TypeInfo_ delegate () createTypeInfo) {
    // First check whether this has already been instanced.
    auto inInstances = args in instances;
    if (inInstances) {
      // Yes, return it.
      return *inInstances;
    } else {
      // No, create the new instance.
      const toRet = globalTypeInfo.length;
      globalTypeInfo ~= createTypeInfo ();
      instances [args] = toRet;
      return toRet;
    }
  }

  TypeId instance (const Value [] args /*, size_t size*/) {
    // Args should have the Kind's expected types.
    if (
      zip (StoppingPolicy.requireSameLength, args.map!`a.type`, argTypes)
        .all! (a => a[0].isSubTypeOf (a[1]))
    ) {
      // Types match.
      return instance (args, () => new ParametrizedTypeInfo (
        &this
        , args
        /*, size //args.map! (a => globalTypeInfo [a.value.get!TypeId].size).sum*/
      ));
    } else {
      throw new Exception (text (
        `Arguments `, args, ` don't match ` ~ baseName, `'s params: `, argTypes
      ));
    }
  }
}

ParametrizedKind ArrayKind;
// For `a to b` expressions.
ParametrizedKind MappingKind;

auto ArrayOf (TypeId type) {
  // TODO: Check size.
  return ArrayKind.instance ([Value (Kind, Var (type))]);
}

auto MappingTo (TypeId sourceType, TypeId destType) {
  return MappingKind.instance ([
    Value (Kind, Var (sourceType)), Value (Kind, Var (destType))
  ]);
}

shared static this () {
  // Primitives:
  Kind = addPrimitive (`Kind`);
  Symbol = addPrimitive (`Symbol`);
  String = addPrimitive (`String`);
  Bool = addPrimitive (`Bool`);
  I8 = addPrimitive (`I8`);
  I16 = addPrimitive (`I16`);
  I32 = addPrimitive (`I32`);
  I64 = addPrimitive (`I64`);
  F32 = addPrimitive (`F32`);
  F64 = addPrimitive (`F64`);
  TupleT = addPrimitive (`Tuple`);
  EmptyArray = addPrimitive (`EmptyArray`);

  // Implicit conversions:
  implicitConversions [F32] = TypeImplicitConversions ([F64]);
  implicitConversions [I32] = TypeImplicitConversions ([F64, I64]);
  implicitConversions [I16] = TypeImplicitConversions ([F32, I32]);
  implicitConversions [I8] = TypeImplicitConversions ([I16]);

  // Intrinsic parametrized types:
  ArrayKind = ParametrizedKind ("Array", [Kind]);
  MappingKind = ParametrizedKind ("Mapping", [Kind, Kind]);
}
