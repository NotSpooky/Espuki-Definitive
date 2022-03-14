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
Value espukiToFun (
  in Value [] inputs
  , in Value [] underscoreArgs
  , ref RuleMatcher ruleMatcher
  // , ref ValueScope valueScope
) {
  assert (inputs.length == 3);
  return toEspuki (Mapping (inputs [0], inputs [2]));
}

Value createAA (
  in Value [] inputs
  , in Value [] underscoreArgs
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
    writeln (`===== Inserting `, mapped, ` into AA`);
    toRet.val [mapped [0]] = mapped [1];
  }
  return toRet.toEspuki (mappingTypes [0], mappingTypes [1]);
}

Value arrayPos (
  in Value [] inputs
  , in Value [] underscoreArgs
  , ref RuleMatcher ruleMatcher
) {
  assert (inputs.length == 3);
  TypeId elementType = inputs [0].type.arrayElementType ();
  return Value (
    elementType
    , inputs [0]
      .extractVar
      .tryMatch!((Var [] asArray) => asArray) [inputs [2].extractVar.tryMatch!((long l) => l)]
  );
}

Value aaGet (
  in Value [] inputs
  , in Value [] underscoreArgs
  , ref RuleMatcher ruleMatcher
) {
  import std.stdio;
  assert (inputs.length == 3);
  TypeId valueType = inputs [0].type.aaValueType ();
  return Value (
    valueType
    , inputs [0]
      .extractVar
      .tryMatch! ((EspukiAA aa) => aa.val) [inputs [2].extractVar]
  );
}

shared static this () {
  // TODO: Make generic
  auto espukiTo = Rule (
    [RuleParam (Any), RuleParam (asSymbol (`to`)), RuleParam (Any)]
    , toDelegate (&espukiToFun)
  );
  auto createAAR = Rule (
    [RuleParam (ArrayKind), RuleParam (`as`.asSymbol), RuleParam (`aa`.asSymbol)]
    , toDelegate (&createAA)
  );
  auto arrayPosIdx = Rule (
    [RuleParam (ArrayKind), RuleParam (`pos`.asSymbol), RuleParam (I64)]
    , toDelegate (&arrayPos)
  );
  auto aaGet = Rule (
    [RuleParam (AAKind), RuleParam (`get`.asSymbol), RuleParam (Any)]
    , toDelegate (&aaGet)
  );
  globalRules = [espukiTo, createAAR, arrayPosIdx, aaGet];
}
