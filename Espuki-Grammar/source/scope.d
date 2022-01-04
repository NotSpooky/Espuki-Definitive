ValueScope globalScope;

import std.exception : enforce;
import std.typecons : Nullable, nullable;
import value : Value, typeToValue;
import type : TypeId, globalTypeInfo, TypeInfo_;

struct ValueScope {
  Nullable!(ValueScope *) parent;
  private Value [string] values;
  TypeId addType (string identifier/*, size_t size*/) {
    Nullable!TypeId toRet;
    this.values.require (
      identifier
      , {
        const typeId = globalTypeInfo.length;
        globalTypeInfo ~= new TypeInfo_ (/*size,*/ identifier);
        toRet = Nullable!TypeId (typeId);
        return typeToValue (typeId);
      } ()
    );
    enforce (
      !toRet.isNull ()
      ,`Type ` ~ identifier ~ ` already exists in the scope`
    );
    return toRet.get ();
  }

  Nullable!Value find (string name) {
    auto pNullable = nullable (&this);
    while (!pNullable.isNull) {
      auto p = pNullable.get ();
      auto nInVals = name in p.values;
      if (nInVals) {
        return nullable (*nInVals);
      }
      pNullable = p.parent;
    }
    return Nullable!Value ();
  }
}
