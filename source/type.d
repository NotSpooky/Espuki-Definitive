module type;

import std.algorithm;
import std.conv;
import std.sumtype;
import std.range;
import std.typecons;
import value;

alias TypeId = size_t;

/+struct TypeImplicitConversions {
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
}+/

//TypeImplicitConversions [TypeId] implicitConversions;

//[Tuple!(Value, `source`, Value, `target`)] 

/+
/// Includes itself and all the types this one can implicitly convert to.
auto visitTypeConvs (TypeId type) {
  auto tInImplicit = type in implicitConversions;
  if (tInImplicit) {
    return (*tInImplicit).visitT (type);
  }
  return [type];
}

+/
/// As of now just handles type equality by id.
bool isSubTypeOf (TypeId type, TypeId parent) {
  if (type == parent) {
    return true;
  }
  debug (2) {
    import std.stdio;
    writeln (`TODO: isSubTypeOf`);
  }
  return false;
}

struct NamedType {
  string name;
  TypeId type;
}

private TypeId addPrimitive (string name) {
  // As of now, all variables will be stored on a Var, so that'll be the size.
  // return globalScope.addType (name, Var.sizeof);
  import value : Var;
  auto thisId = globalTypeInfo.length;
  globalTypeInfo [thisId] = new TypeInfo_ (/*Var.sizeof,*/ name);
  return thisId;
}

// Initialized on module constructor.
TypeId Any;    // Contains whatever.
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
TypeId Code;
TypeId ParameterlessFunction;

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

private class ParametrizedTypeInfo : TypeInfo_ {
  const ParametrizedKind * kind;
  const Value [] args;
  this (ParametrizedKind * kind, const Value [] args /*, size_t size */) {
    assert (kind !is null);
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

TypeInfo_ [TypeId] globalTypeInfo;
ParametrizedKind [] globalParametrizedKinds;

bool isParametrizedFrom (TypeId type, in ParametrizedKind * kind) {
  auto typeInfo = globalTypeInfo [type];
  if (auto asParametrized = (cast (ParametrizedTypeInfo) typeInfo)) {
    return asParametrized.kind.id == kind.id;
  } else {
    return false;
  }
}

/// Used to create parametrized types.
struct ParametrizedKind {
  uint id;
  TypeId [] argTypes;
  string baseName;
  TypeId [Value []] instances;
  @disable this ();
  this (uint id, string baseName, TypeId [] argTypes) {
    this.id = id;
    this.baseName = baseName;
    this.argTypes = argTypes;
  }

  // Version that adds a custom TypeInfo for this type.
  TypeId instance (const Value [] args, TypeInfo_ delegate () createTypeInfo) {
    // First check whether this has already been instanced.
    auto inInstances = args in instances;
    if (inInstances) {
      // Yes, return it.
      return *inInstances;
    } else {
      // No, create the new instance.
      const toRet = globalTypeInfo.length;
      globalTypeInfo [toRet] = createTypeInfo ();
      this.instances [args] = toRet;
      return toRet;
    }
  }

  // Basic version whose type info just includes the corresponding ParametrizedKind
  TypeId instance (const Value [] args /*, size_t size*/) {
    // Args should have the Kind's expected types.
    if (
      zip (StoppingPolicy.requireSameLength, args.map!`a.type`, argTypes)
        .map! (a => a[0].isSubTypeOf (a[1]))
        .all ()
    ) {
      // Types match.
      return instance (args, () => new ParametrizedTypeInfo (
        & this
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

ParametrizedKind * addParametrizedKind (string baseName, TypeId [] argTypes) {
  import value : Var;
  globalParametrizedKinds ~= ParametrizedKind (
    globalParametrizedKinds.length.to!uint, baseName, argTypes
  );
  return &globalParametrizedKinds [$-1];
}

ParametrizedKind * ArrayKind;
// For `a to b` expressions.
ParametrizedKind * MappingKind;
ParametrizedKind * AAKind;
ParametrizedKind * FunctionKind;


auto arrayOf (TypeId type) {
  // TODO: Check size.
  return ArrayKind.instance ([Value (Kind, Var (type))]);
}

auto associativeArrayOf (TypeId keyType, TypeId valueType) {
  return AAKind.instance (
    [Value (Kind, Var (keyType)), Value (Kind, Var (valueType))]
  );
}

auto functionOf (TypeId [] types, TypeId returnType) {
  return FunctionKind.instance ([
    Value (arrayOf(Kind), Var (types.map! (type => Var (type)).array))
    , Value (Kind, Var (returnType))
  ]);
}

auto isFunction (TypeId type) {
  return type.isParametrizedFrom (FunctionKind);
}

TypeId getElementParameter (TypeId type, size_t index) {
  auto argType = (cast (ParametrizedTypeInfo) globalTypeInfo [type])
    .args [index];
  assert (argType.type == Kind);
  return argType.extractVar ().tryMatch! ((TypeId t) => t);
}

TypeId arrayElementType (TypeId arrayType) {
  // Type must be an array.
  return getElementParameter (arrayType, 0);
}

TypeId aaValueType (TypeId aaType) {
  // Type must be an aa.
  return getElementParameter (aaType, 1);
}

TypeId [2] mappingElementTypes (TypeId mappingType) {
  // Type must be a mapping.
  auto mappingArgs = (cast (ParametrizedTypeInfo) globalTypeInfo [mappingType]).args;
  assert (mappingArgs.length == 2);
  assert (mappingArgs [0].type == Kind);
  assert (mappingArgs [1].type == Kind);
  return [
    mappingArgs [0].extractVar ().tryMatch! ((TypeId t) => t),
    mappingArgs [1].extractVar ().tryMatch! ((TypeId t) => t)
  ];
}

auto MappingTo (TypeId sourceType, TypeId destType) {
  return MappingKind.instance ([
    Value (Kind, Var (sourceType)), Value (Kind, Var (destType))
  ]);
}

shared static this () {
  // Primitives:
  Any = addPrimitive (`Any`);
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
  Code = addPrimitive (`Code`);

  /+
  // Implicit conversions:
  implicitConversions [F32] = TypeImplicitConversions ([F64]);
  implicitConversions [I32] = TypeImplicitConversions ([F64, I64]);
  implicitConversions [I16] = TypeImplicitConversions ([F32, I32]);
  implicitConversions [I8] = TypeImplicitConversions ([I16]);
  +/

  // Intrinsic parametrized types:
  ArrayKind = addParametrizedKind ("Array", [Kind]);
  MappingKind = addParametrizedKind ("Mapping", [Kind, Kind]);
  AAKind = addParametrizedKind ("AssociativeArray", [Kind, Kind]);
  FunctionKind = addParametrizedKind ("Function", [arrayOf (Kind), Kind]);

  // This requires FunctionKind to exist.
  ParameterlessFunction = functionOf ([], I64);
}
