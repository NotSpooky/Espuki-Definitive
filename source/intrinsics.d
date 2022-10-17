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
  ref InterpretedValue [] inputs
  , ref RuleMatcher ruleMatcher
  // , ref ValueScope valueScope
) {
  assert (inputs.length == 3);
  return toEspuki (Mapping (inputs [0], inputs [2]));
}

InterpretedValue createAA (
  ref InterpretedValue [] inputs
  , ref RuleMatcher ruleMatcher
) {
  // Should this be == 3?
  assert (inputs.length >= 3);
  TypeId typeMapping = arrayElementType (inputs [0].type);
  TypeId [2] mappingTypes = mappingElementTypes (typeMapping);
  EspukiAA toRet;
  
  auto asArray = inputs [0]
    .extractVar ()
    .tryMatch! ((Value [] vars) => vars)
    .map! (var => var
      .extractVar
      //.tryMatch!((VarWrapper vw) => vw)
      .tryMatch!((Var [] mapping) => mapping)
    );
  foreach (mapped; asArray) {
    assert (mapped.length == 2);
    writeln (`===== Inserting `, mapped [0], ` -> `, mapped [1], ` into AA`);
    toRet.val [VarWrapper (mapped [0])] = mapped [1];
  }
  return toRet.toEspuki (mappingTypes [0], mappingTypes [1]);
}

InterpretedValue arrayPos (
  ref InterpretedValue [] inputs
  , ref RuleMatcher ruleMatcher
) {
  assert (inputs.length == 3);
  TypeId elementType = inputs [0].type.arrayElementType ();
  writeln(inputs [0].extractVar);
  writeln(elementType);
  return InterpretedValue (
    elementType
    , inputs [0]
      .extractVar ()
      .tryMatch! ((Value [] asArray) => asArray)
      [inputs [2].extractVar.tryMatch!((long l) => l)]
      .extractVar
  );
}

InterpretedValue aaGet (
  ref InterpretedValue [] inputs
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

InterpretedValue intSum (
  ref InterpretedValue [] inputs
  , ref RuleMatcher ruleMatcher
) {
  assert (inputs.length == 3);
  assert (inputs [0].type == I64);
  assert (inputs [2].type == I64);
  return InterpretedValue (
    I64
    , Var (
        inputs [0]
        .extractVar ()
        .tryMatch! ((long l) => l)
        + inputs [2]
        .extractVar ()
        .tryMatch! ((long l) => l)
      )
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
  auto intAdd = Rule (
    [RuleParam (I64), RuleParam (`+`), RuleParam (I64)]
    , toDelegate (&intSum)
  );

  globalRules = [espukiTo, createAAR, arrayPosIdx, aaGet, intAdd];
}
