module rulematcher;

import std.algorithm;
import std.range;
import mir.algebraic;
import std.conv : text, to;
debug import std.stdio;
import intrinsics;
import execute;

alias RuleValue = Variant! (TypeId, RTValue, EndOfRule);
const eor = RuleValue (EndOfRule());
alias RuleParam = Variant! (TypeId, RTValue);
string toString (RuleParam rp) {
  import execute : toString;
  return rp.visit! (
    (RTValue val) => val.to!string
    , (TypeId type) => toString (type)
  );
}

alias SetOfRuleP = bool [Rule *];

auto ruleFrom (RuleParam [] vals) {
  return Rule (
    vals
    , (
      in RTValue [] inputs
      , ref RuleMatcher ruleMatcher
      , ref ValueScope valueScope
    ) {
      return RTValue (I32, Var (999));
    }
  );
}

auto toRuleValue (RuleParam ruleParam) {
  return ruleParam.visit! (a => RuleValue (a));
}
unittest {
  auto rules = RuleMatcher ([]);
  auto rule1Params = [RuleParam (I32), RuleParam (I32)];
  auto example1 = ruleFrom (rule1Params);
  rules.addRule (&example1);
  auto args1 = [RTValue (I32, Var (1)), RTValue (I32, Var (2))];
  assert (rules.matchRule (args1) == example1);
  auto rule2Params = rule1Params ~ [RuleParam (String)];
  auto example2 = ruleFrom (rule2Params);
  rules.addRule (&example2);
  auto args2 = args1 ~ RTValue (String, Var (`Olis`));
  assert (rules.matchRule (args2) == example2);
  assert (rules.matchRule (args1) == example1);
  auto rule3Params = [RuleParam (I64), RuleParam (I32)];
  auto example3 = ruleFrom (rule3Params);
  rules.addRule (&example3);
  assert (rules.matchRule (args1) == example1);
  auto args3 = [RTValue (I64, Var (500L)), RTValue (I32, Var (4))];
  assert (rules.matchRule (args3) == example3);
}
struct EndOfRule {}

struct RuleMatcher {
  SetOfRuleP [RuleValue] [] setsForPositions;

  this (ref Rule [] rules) {
    foreach (ref rule; rules) {
      this.addRule (& rule);
    }
  }

  auto addRule (Rule * toAdd) {
    const rValLen = toAdd.params.length;
    if (setsForPositions.length < rValLen + 1) {
      setsForPositions.length = rValLen + 1;
    }
    foreach (i, ruleVal; toAdd.params.map!toRuleValue.enumerate) {
      setsForPositions [i][ruleVal][toAdd] = true;
    }
    setsForPositions [rValLen][eor][toAdd] = true;
  }

  private auto rulesMatching (alias OnSet)(in TypeId type, size_t index) const {
    // Note: visitTypeConvs includes itself, so no checking for RuleValue (type)
    // is needed.
    foreach (generalType; type.visitTypeConvs ()) {
      const genValInSet = RuleValue (generalType) in setsForPositions [index];
      if (genValInSet) {
        OnSet (*genValInSet);
      }
    }
  }

  private void rulesMatching (alias OnSet)(in RTValue val, size_t index) const {
    auto valInSet = RuleValue (val) in setsForPositions [index];
    if (valInSet) {
      OnSet (*valInSet);
    }
    foreach (generalType; val.type.visitTypeConvs ()) {
      const convValInSet
        = RuleValue (val.tryImplicitConversion (generalType))
          in setsForPositions [index];
      if (convValInSet) {
        OnSet (*convValInSet);
      }
    }
    // Also match types.
    rulesMatching!OnSet (val.type, index);
  }

  /// Advances inputs.
  RTValue matchAndExecuteRule (ref RTValue [] inputs, ref ValueScope valueScope) {
    auto matched = this.matchRule (inputs);
    RTValue toRet = matched.applyFun (inputs, this, valueScope);
    inputs = inputs [matched.params.length .. $];
    return toRet;
  }


  const (Rule) matchRule (ref RTValue [] inputs) {
    assert (inputs.length > 0);
    const (Rule) * [] matches;
    SetOfRuleP possibleMatches;
    // Fill possibleMatches.
    rulesMatching! ((s) {
      foreach (ruleP; s.keys) {
        possibleMatches [ruleP] = true;
      }
    }) (inputs [0], 0);
    // debug writeln (`Possible matches is `, possibleMatches);

    foreach (i, ruleVal; inputs [1..$]) {
      if (setsForPositions.length == i) {
        break;
      }
      // debug writeln (`Matching `, ruleVal);
      //debug writeln (`POS `, i);
      // For next iteration.
      SetOfRuleP savedPossibleMatches;
      rulesMatching! ((setOfRules) {
        // TODO: Optimization: use the smallest set for the loop.
        //debug writeln (`Got a matching set of rules! `, setOfRules);
        foreach (ruleP; possibleMatches.keys) {
          if (ruleP in setOfRules) {
            savedPossibleMatches [ruleP] = true;
          }
        }
      }) (ruleVal, i + 1);
      
      // Also check for rule end.
      auto endingRulesAtPos = eor in setsForPositions [i + 2];
      //debug writeln (`Eor in next pos? `, endingRulesAtPos);
      if (endingRulesAtPos) {
        // Check in possible matches because savedPossibleMatches doesn't
        // know about the eoc.
        auto endFound = possibleMatches.keys.filter! (
          k => k in * endingRulesAtPos
        ).array;
        //debug writeln (`End found `, endFound);
        if (!endFound.empty) {
          // Bigger matches have priority, so discard all the previous ones.
          matches = endFound;
          foreach (e; endFound) {
            // No need to keep matching for rules we already matched.
            savedPossibleMatches.remove (e);
          }
        }
      }
      possibleMatches = savedPossibleMatches;
      // Exhausted possibilities.
      // All matches found are stored on 'matched'.
      if (possibleMatches.empty) {
        break;
      }
    }
    
    // Let's validate the matches.
    matches = matches.filter! (m => 
      m.params.enumerate.all! ((r) {
        auto dir = inputs [r [0]].implicitDir (r[1]);
        return dir == ImplicitConversionDirection.firstToSecond
          || dir == ImplicitConversionDirection.twoAreTheSame;
      })
    ).array;

    // Now let's check for specializations.
    if (matches.empty) {
      throw new Exception (`No rule found for ` ~ inputs.to!string);
    }
    auto bestMatch = matches.front;
    matches.popFront ();
    enum SpecializationDir {
      unknown, alternativeIsSpec, bestMatchIsSpec
    }
    foreach (alternative; matches) { 
      with (SpecializationDir) {
        auto specDir = unknown;
        // Another option is to have specialization info on the same rules.
        foreach (best, alt; bestMatch.params.lockstep (alternative.params)) {
          auto dir = implicitDir (best, alt);
          debug writeln (`Comparing `, toString (best), ` with `, toString (alt));
          debug writeln (dir);
          with (ImplicitConversionDirection) {
            if (
              dir == noConversionPossible
                || (
                  // Cannot have specializations in both directions.
                  dir == firstToSecond && specDir == bestMatchIsSpec
                ) || (
                  // ditto.
                  dir == secondToFirst && specDir == alternativeIsSpec
                )
            ) {
              throw new Exception (text (
                `Multuple rules match `, inputs, ":\n", bestMatch, '\n', alternative
              ));
            } else if (dir == firstToSecond) {
              specDir = bestMatchIsSpec;
            } else if (dir == secondToFirst) {
              specDir = alternativeIsSpec;
            }
          }
        }
        assert (specDir != unknown);
        if (specDir == alternativeIsSpec) {
          bestMatch = alternative;
        }
      }
    }
    return *bestMatch;
  }
}

enum ImplicitConversionDirection {
  noConversionPossible
  , firstToSecond
  , secondToFirst
  , twoAreTheSame
}

alias implicitDir = match!(
  (RTValue firstValue, RTValue secondValue) {
    auto firstType = firstValue.type;
    auto secondType = secondValue.type;
    if (firstType.isSubTypeOf (secondType)) {
      if (
        firstValue.tryImplicitConversion (secondType).value == secondValue.value
      ) {
        if (firstType == secondType) {
          return ImplicitConversionDirection.twoAreTheSame;
        } else {
          return ImplicitConversionDirection.firstToSecond;
        }
      }
    } else {
      if (secondType.isSubTypeOf (firstType)) {
        if (
          secondValue.tryImplicitConversion (firstType).value == firstValue.value
        ) {
          return ImplicitConversionDirection.secondToFirst;
        }
      }
    }
    return ImplicitConversionDirection.noConversionPossible;
  }
  , (RTValue firstValue, TypeId secondType) {
    if (firstValue.type.isSubTypeOf (secondType)) {
      return ImplicitConversionDirection.firstToSecond;
    }
    return ImplicitConversionDirection.noConversionPossible;
  }
  , (TypeId firstType, RTValue secondValue) {
    if (secondValue.type.isSubTypeOf (firstType)) {
      return ImplicitConversionDirection.secondToFirst;
    }
    return ImplicitConversionDirection.noConversionPossible;
  }
  , (TypeId firstType, TypeId secondType) {
    if (firstType == secondType) {
      return ImplicitConversionDirection.twoAreTheSame;
    } else if (firstType.isSubTypeOf (secondType)) {
      return ImplicitConversionDirection.firstToSecond;
    } else if (secondType.isSubTypeOf (firstType)) {
      return ImplicitConversionDirection.secondToFirst;
    } else {
      return ImplicitConversionDirection.noConversionPossible;
    }
  }
);
