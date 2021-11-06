alias TypeId = size_t;

struct NamedType {
  string name;
  TypeId type;
}

class TypeInfo_ {
  const size_t size;
  string name;
  this (size_t size, string name) {
    this.size = size;
    this.name = name;
  }
  override string toString () {
    return name;
  }
}

TypeInfo_ [] globalTypeInfo;

private int lastTypeId = 0;
private TypeId addPrimitive (string name) {
  // As of now, all variables will be stored on a Var, so that'll be the size.
  // return globalScope.addType (name, Var.sizeof);
  import value : Var;
  globalTypeInfo ~= new TypeInfo_ (Var.sizeof, name);
  return globalTypeInfo.length - 1;
}

TypeId Kind; // Just a Type of Type.
TypeId String;
TypeId Float;
TypeId I64;
TypeId TupleT;

shared static this () {
  // Primitives:
  Kind = addPrimitive (`Kind`);
  String = addPrimitive (`String`);
  Float = addPrimitive (`Float`);
  I64 = addPrimitive (`I64`);
  TupleT = addPrimitive (`Tuple`);
}
