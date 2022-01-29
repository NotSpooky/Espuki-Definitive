module intrinsics;

import std.functional : toDelegate;
import rule;
import type;
import scopes;
import value;

Rule [] globalRules;

Value espukiToFun (
  in Value [] inputs
  , in Value [] underscoreArgs
  , ref RuleMatcher ruleMatcher
  // , ref ValueScope valueScope
) {
  assert (inputs.length == 3);
  return toEspuki(Mapping(inputs [0], inputs [2]));
}

shared static this () {
  // TODO: Make generic
  auto espukiTo = Rule (
    [RuleParam(String), RuleParam(asSymbol(`to`)), RuleParam(String)], toDelegate(&espukiToFun)
  );
  globalRules = [espukiTo];
}
