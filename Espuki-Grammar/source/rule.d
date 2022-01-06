import std.sumtype;
import std.typecons : Nullable;
import value : Value;
import type : TypeId;

struct RuleMatcher {
  Value match (T)(T toMatch) {
    import std.stdio;
    writeln (`DEB: Matching `, toMatch);

    import type : I64;
    import value : Var;
    return Value (I64, Var(777));
  }
}

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

//alias RuleValue = SumType! (TypeId, Value, EndOfRule);
alias RuleParam = SumType! (TypeId, Value);

struct Rule {
  @disable this ();
  RuleParam [] params;
  ApplyFun applyFun;
}
