module rule;

import std.algorithm;
import std.range;
import std.sumtype;
import std.typecons : Nullable;
import value : Value;
import type : TypeId;

// Used for rule declarations.
alias RuleParam = SumType! (TypeId, Value);
// Parsed text is converted to RuleArgs to match with RuleParams.
alias RuleArg = SumType! (TypeId, Value);

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

struct NoMatch {}

enum MatchType {
  // E.g. A rule has an 'I32 42' parameter and the argument matched is 'I32 42'.
  exactValueMatch
  // E.g. A rule has an 'I32' parameter and the argument matched is 'I32 42'.
  // This also applies to matching typeclasses.
  , exactTypeMatch
  // E.g. A rule has an 'I64' parameter and the argument matched is 'I32 42'.
  , parentTypeMatch
  // E.g. A rule has a 'Bool' parameter and the argument matched is 'I32 42'.
  , noMatch
}

private alias MatchScores = SumType! (MatchType [], NoMatch);

MatchScores score (T)(in T toMatch, in Rule rule) {
  if (toMatch.length < rule.params.length) {
    return MatchScores (NoMatch ());
  }
  auto matchScores = new MatchType [rule.params.length];
  auto toRet = MatchScores(matchScores);
  foreach (i, param; rule.params) {
    auto matchType = param.match!(
      (TypeId type) {
        return type == toMatch [i].type ? MatchType.exactTypeMatch : MatchType.noMatch;
        // TODO: Parent type match.
      },
      (const Value val) {
        // Exact value.
        return toMatch[i] == val ? MatchType.exactValueMatch : MatchType.noMatch;
      }
    );
    if (matchType == MatchType.noMatch) {
      return MatchScores (NoMatch ());
    }
    matchScores [i] = matchType;
  }
  return toRet;
}

struct RuleMatcher {
  Value match (T)(T toMatch, Rule [] rules) if (is (typeof(toMatch.front) == Value)) {
    import std.stdio;
    writeln (`DEB: Matching `, toMatch);
    writeln (`DEB: With rules: `, rules);
    foreach (rule; rules) {
      writeln ("Rule match score:", rule, " ", score (toMatch, rule));
    }
    
    // TODO: Delete
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
