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
  auto applyRule (Value [] args, Value [] underscoreArgs, ref RuleMatcher ruleMatcher) {
    debug (2) {
      // TODO: Take into account underscoreArgs
      assert (score (args, this).match! ((Scores s) => true, (NoMatch nm) => false));
    }
    size_t pLen = this.params.length;
    assert (pLen <= args.length);
    return this.applyFun (args [0 .. pLen], underscoreArgs, ruleMatcher);
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
  size_t rulePos;
}
private alias MatchScores = SumType! (Scores, NoMatch);

/// Takes a list of values to match against the rule.
/// Returns a wrapped list (Scores) that corresponds to how good the match was 
/// at each position.
/// If the rule doesn't match, a NoMatch is returned instead.
MatchScores score (in Value [] toMatch, in Rule rule, size_t rulePos) {
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
  return MatchScores (Scores (matchScores, rulePos));
}

/// Returns a list containing the best matches for the input at the position 'index'.
private size_t [] bestOfIndex (size_t index, Scores [] matchedRules) {
  size_t [] bestOfThisIndex;
  MatchType currentBestMatchType = MatchType.parentTypeMatch;
  foreach (m, matchedRule; matchedRules) {
    auto matchScore = matchedRule.scores [index];
    if (matchScore < currentBestMatchType) {
      bestOfThisIndex = [m];
    } else if (matchScore == currentBestMatchType) {
      bestOfThisIndex ~= m;
    }
  }
  return bestOfThisIndex;
}

struct RuleMatcher {
  /// A rule must be the best match in all positions to be the best.
  /// If some rule has the best match in a position but not in another, it's
  /// ambiguous which one to use so an error is returned.
  /// Returns the position in the rules that corresponds to the best matching one.
  size_t match (Value [] toMatch, ref Rule [] rules) {
    assert (rules.length > 0, `No rules to match`);

    import std.stdio;
    writeln (`DEB: Matching `, toMatch);
    writeln (`DEB: With rules: `, rules);
    // TODO: Get only the longest matches
    auto matchedRules = rules
      .enumerate
      .map!(rule => score (toMatch, rule [1], rule [0]))
      .filter!(score => score.match! ((Scores s) => true, (NoMatch s) => false))
      .map!(score => score.tryMatch! ((Scores a) => a))
      .tee!(score => assert (score.scores.length > 0, `Got an empty score list`))
      .array;

    import std.conv : to, text;
    if (matchedRules.empty) {
      throw new Exception (`No rules match ` ~ toMatch.to!string);
    }
    auto firstIndexBest = bestOfIndex (0, matchedRules);
    assert (firstIndexBest.length > 0);
    // Used as a set
    bool [size_t] bestMatchPositions;
    // Fill the set with the rules that are the best match at the first position.
    foreach (bestOfFirst; firstIndexBest) {
      bestMatchPositions [bestOfFirst] = true;
    }

    // Prune on each subsequent position the matches that aren't the best ones.
    foreach (i; 1 .. matchedRules.front.scores.length) {
      size_t [] bestOfThisIndex = bestOfIndex (i, matchedRules);
      assert (bestOfThisIndex.length > 0);
      foreach (bestOfThisPos; bestOfThisIndex) {
        if (bestOfThisPos !in bestMatchPositions) {
          bestMatchPositions.remove (bestOfThisPos);
        }
      }
    }

    auto bestMatchesInAllPositions = bestMatchPositions.byKey().array();
    if (bestMatchesInAllPositions.length == 1) {
      writeln (`DEB: Best rule position is `, bestMatchesInAllPositions [0]);
      writeln (`DEB: Matching rules are `, matchedRules);
      size_t toRet = matchedRules [bestMatchesInAllPositions [0]].rulePos;
      return toRet;
    }

    auto rulesInBestMatches () {
      return matchedRules
        .indexed (bestMatchesInAllPositions)
        .map! (m => rules [m.rulePos]);
    }

    if (matchedRules.length > 1) {
      throw new Exception (text (
        `Multiple rules match `, toMatch, `: `, rulesInBestMatches ()
      ));
    } else {
      bestMatchPositions.clear;

      foreach (i; 0 .. matchedRules.front.scores.length) {
        foreach (bestOfThisIndexPos; bestOfIndex (i, matchedRules)) {
          bestMatchPositions [bestOfThisIndexPos] = true;
        }
      }
      // There's an ambiguity. Get the rules with best matches.
      throw new Exception (text (
        `Ambiguity choosing between rules: `, rulesInBestMatches ()
      ));
    }
  }
}
