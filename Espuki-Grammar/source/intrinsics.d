module intrinsics;

import std.algorithm;
import std.functional : toDelegate;
import std.sumtype;
import rule;
import type;
import scopes;
import value;
debug import std.stdio;

Rule [] globalRules;

// Used to create Mappings, mostly used to create associative arrays/dicts.
InterpretedValue espukiToFun (
  in InterpretedValue [] inputs
  , ref RuleMatcher ruleMatcher
  // , ref ValueScope valueScope
) {
  assert (inputs.length == 3);
  return toEspuki (Mapping (inputs [0], inputs [2]));
}

InterpretedValue createAA (
  in InterpretedValue [] inputs
  , ref RuleMatcher ruleMatcher
) {
  assert (inputs.length == 3);
  TypeId typeMapping = arrayElementType (inputs [0].type);
  TypeId [2] mappingTypes = mappingElementTypes (typeMapping);
  EspukiAA toRet;
  
  auto asArray = inputs [0]
    .extractVar ()
    .tryMatch! ((Var [] vars) => vars)
    .map! (var => var.tryMatch!((Var [] mapping) => mapping));
  foreach (mapped; asArray) {
    assert (mapped.length == 2);
    writeln (`===== Inserting `, mapped [0], ` -> `, mapped [1], ` into AA`);
    toRet.val [VarWrapper (mapped [0])] = mapped [1];
  }
  return toRet.toEspuki (mappingTypes [0], mappingTypes [1]);
}

InterpretedValue arrayPos (
  in InterpretedValue [] inputs
  , ref RuleMatcher ruleMatcher
) {
  assert (inputs.length == 3);
  TypeId elementType = inputs [0].type.arrayElementType ();
  return InterpretedValue (
    elementType
    , inputs [0]
      .extractVar
      .tryMatch!((Var [] asArray) => asArray)
      [inputs [2].extractVar.tryMatch!((long l) => l)]
  );
}

InterpretedValue aaGet (
  in InterpretedValue [] inputs
  , ref RuleMatcher ruleMatcher
) {
  assert (inputs.length == 3);
  TypeId valueType = inputs [0].type.aaValueType ();
  return InterpretedValue (
    valueType
    , inputs [0]
      .extractVar
      .tryMatch! ((const EspukiAA aa) => aa.val)
      [VarWrapper (inputs [2].extractVar)]
  );
}

shared static this () {
  // TODO: Make generic
  auto espukiTo = Rule (
    [RuleParam (Any), RuleParam (`to`), RuleParam (Any)]
    , toDelegate (&espukiToFun)
  );
  auto createAAR = Rule (
    [RuleParam (ArrayKind), RuleParam (`as`), RuleParam (`aa`)]
    , toDelegate (&createAA)
  );
  auto arrayPosIdx = Rule (
    [RuleParam (ArrayKind), RuleParam (`pos`), RuleParam (I64)]
    , toDelegate (&arrayPos)
  );
  auto aaGet = Rule (
    [RuleParam (AAKind), RuleParam (`get`), RuleParam (Any)]
    , toDelegate (&aaGet)
  );
  globalRules = [espukiTo, createAAR, arrayPosIdx, aaGet];
}
