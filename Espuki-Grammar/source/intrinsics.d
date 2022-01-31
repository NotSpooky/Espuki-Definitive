module intrinsics;

import std.functional : toDelegate;
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
  return toEspuki(Mapping(inputs [0], inputs [2]));
}

// NOTE: Due to limitations with the hash of Vars, we use void* here.
Value createAA (
  in Value [] inputs
  , in Value [] underscoreArgs
  , ref RuleMatcher ruleMatcher
) {
  assert (inputs.length == 2);
  TypeId typeMapping = arrayElementType (inputs [1].type);
  TypeId [2] mappingTypes = mappingElementTypes (typeMapping);
  void * [void *] toRet;
  // TODO: Fill with inputs.
  return toEspuki (toRet, mappingTypes [0], mappingTypes [1]);
}

shared static this () {
  // TODO: Make generic
  auto espukiTo = Rule (
    [RuleParam (String), RuleParam (asSymbol (`to`)), RuleParam (String)]
    , toDelegate (&espukiToFun)
  );
  auto createAAR = Rule (
    [RuleParam(asSymbol (`aa`)), RuleParam(asSymbol (`of`)), RuleParam(MappingTo (String, String))]
    , toDelegate (&createAA)
  );
  globalRules = [espukiTo, createAAR];
}
