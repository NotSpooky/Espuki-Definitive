module intrinsics;

import std.functional : toDelegate;
import rule;
import type;
import value;

Rule [] globalRules;

Value espukiToFun (
  in Value [] inputs
  , in Value [] underscoreArgs
  , ref RuleMatcher ruleMatcher
  , ref ValueScope valueScope
) {
  return asSymbol(`Spooks`);
}

static this () {
  // TODO: Make generic
  auto espukiTo = Rule (
    [RuleParam(String), RuleParam(asSymbol(`to`)), RuleParam(String)], toDelegate(&espukiToFun)
  );
  globalRules = [espukiTo];
}
