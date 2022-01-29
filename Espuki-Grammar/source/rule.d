module rule;

import std.algorithm;
import std.range;
import std.sumtype;
import std.typecons : Nullable;
import value : Value;
import type : TypeId;
import scopes;

// Used for rule declarations.
alias RuleParam = SumType! (TypeId, Value);

alias ApplyFun = Value delegate (
  in Value [] inputs
  , in Value [] underscoreArgs
  , ref RuleMatcher ruleMatcher
  // , ref ValueScope valueScope
);

struct Rule {
  @disable this ();
  RuleParam [] params;
  private ApplyFun applyFun;
  this (RuleParam [] params, ApplyFun applyFun) {
    this.params = params;
    this.applyFun = applyFun;
  }
  // ONLY use if the rule matches.
  auto apply (Value [] args, Value [] underscoreArgs, ref RuleMatcher ruleMatcher) {
    return this.applyFun (args [0 .. this.params.length], underscoreArgs, ruleMatcher);
  }
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

private struct Scores {
  MatchType [] scores;
  Rule * rule;
}
private alias MatchScores = SumType! (Scores, NoMatch);

MatchScores score (T)(in T toMatch, ref Rule rule) {
  if (toMatch.length < rule.params.length) {
    return MatchScores (NoMatch ());
  }
  auto matchScores = new MatchType [rule.params.length];
  foreach (i, param; rule.params) {
    auto elementScore = param.match!(
      (TypeId type) {
        return type == toMatch [i].type ? MatchType.exactTypeMatch : MatchType.noMatch;
        // TODO: Parent type match.
      },
      (const Value val) {
        // Exact value.
        return toMatch[i] == val ? MatchType.exactValueMatch : MatchType.noMatch;
      }
    );
    if (elementScore == MatchType.noMatch) {
      return MatchScores (NoMatch ());
    }
    matchScores [i] = elementScore;
  }
  return MatchScores (Scores (matchScores, &rule));
}

struct RuleMatcher {
  Rule * match (T)(T toMatch, Rule [] rules) if (is (typeof(toMatch.front) == Value)) {
    import std.stdio;
    writeln (`DEB: Matching `, toMatch);
    writeln (`DEB: With rules: `, rules);
    auto matchedRules = rules
      .map!(rule => score (toMatch, rule));
      //.filter!(score => score.match! ((Scores) => true, (NoMatch) => false))
      //.map!(score => score.tryMatch! ((Scores a) => a))
      //.tee!(score => assert (score.length > 0, `Got an empty score list`))
      //.array;
    /*
    if (matchedRules.empty) {
      import std.conv : to;
      throw new Exception (`No rules match ` ~ toMatch.to!string);
    }
    auto firstPossibleMatch = matchedRules.front;
    if (matchedRules.length == 1) {
      return firstPossibleMatch.rule;
    }
    bool [size_t] bestMatchPositions;
    size_t [] bestPositionsOfThisPos;
    foreach (i; 0 .. firstPossibleMatch.length) {
      
    }
    
    // TODO: Delete
    import type : I64;
    import value : Var;
    return Value (I64, Var(777));
    */
    writeln (`DEB: Returning first rule as DEBUG`);
    return & rules [0];
  }
}
