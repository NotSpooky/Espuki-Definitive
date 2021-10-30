alias TypeId = size_t;
TypeId Kind; // Just a Type of Type. // TODO: Set value.

struct NamedType {
  string name;
  TypeId type;
}

class TypeInfo_ {
  const size_t size;
  this (size_t size) {
    this.size = size;
  }
}
TypeInfo_ [] globalTypeInfo;

string toString (TypeId type) {
  return globalTypeInfo [type].toString ();
}

private int lastTypeId = 0;
private TypeId addPrimitive (string name) {
  // As of now, all variables will be stored on a Var, so that'll be the size.
  // return globalScope.addType (name, Var.sizeof);
  import value : Var;
  globalTypeInfo ~= new TypeInfo_ (Var.sizeof);
  return globalTypeInfo.length - 1;
}

TypeId String;
TypeId Float;
TypeId I64;

shared static this () {
  // Primitives:
  String = addPrimitive (`String`);
  Float = addPrimitive (`Float`);
  I64 = addPrimitive (`I64`);
}
