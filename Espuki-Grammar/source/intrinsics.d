module intrinsics;

import std.algorithm;
import std.functional : toDelegate;
import std.sumtype;
import rule;
import type;
import scopes;
import value;

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
  
  // TODO: Fill with inputs.
  auto asArray = inputs [0]
    .extractVar ()
    .tryMatch!((Var [] vars) => vars)
    .map!(var => var.tryMatch!((Var [] mapping) => mapping));
  // return toEspuki (toRet, mappingTypes [0], mappingTypes [1]);
  foreach (mapped; asArray) {
    assert (mapped.length == 2);
    toRet.val [mapped [0]] = mapped [1];
  }
  return toRet.toEspuki (mappingTypes [0], mappingTypes [1]);
}

shared static this () {
  // TODO: Make generic
  auto espukiTo = Rule (
    [RuleParam (String), RuleParam (asSymbol (`to`)), RuleParam (String)]
    , toDelegate (&espukiToFun)
  );
  auto createAAR = Rule (
    [RuleParam (ArrayKind), RuleParam (`as`.asSymbol), RuleParam (`aa`.asSymbol)]
    , toDelegate (&createAA)
  );
  globalRules = [espukiTo, createAAR];
}
