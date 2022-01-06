module rule;

import std.range;
import std.sumtype;
import std.typecons : Nullable;
import value : Value;
import type : TypeId;

struct EndOfRule {}
// Used for rule declarations.
alias RuleParam = SumType! (TypeId, Value, EndOfRule);
// Parsed text is converted to RuleArgs to match with RuleParams.
alias RuleArg = SumType! (TypeId, Value);

struct RuleMatcher {
  Value match (T)(T toMatch) if (is (typeof(toMatch.front) == Value)) {
    import std.stdio;
    writeln (`DEB: Matching `, toMatch);
    
    import type : I64;
    import value : Var;
    return Value (I64, Var(777));
  }
}

// TODO: Move to scope
struct ValueScope {
  Nullable!(ValueScope *) parent;
  private Value [string] values;
}

alias ApplyFun = Value delegate (
  in Value [] inputs
  , in Value [] underscoreArgs
  , ref RuleMatcher ruleMatcher
  , ref ValueScope valueScope
);

struct Rule {
  @disable this ();
  RuleParam [] params;
  ApplyFun applyFun;
}
