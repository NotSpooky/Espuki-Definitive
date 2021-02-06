module functree;

import std.algorithm;
import std.range;
import mir.algebraic;
import std.conv : text, to;
debug import std.stdio;
import intrinsics;

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
struct Rule2 {
  string r;
  RuleParam [] params;
  @disable this ();
  this (string r, RuleParam [] params) {
    this.r = r;
    this.params = params;
  }
}

alias SetOfRuleP = bool [Rule2 *];

import execute;
unittest {
  auto rules = Rules ([]);
  void testRule (RuleValue [] vals) {
    rules.matchRule (vals ~ [eor]).writeln ();
  }
  auto ruleFrom (string r, RuleValue [] vals) {
    return Rule2 (
      r
      , vals
        .tee! (a => assert (!a._is!EndOfRule))
        .map! (a => a.visit! (
          (EndOfRule e) => RuleParam (I8)
          , (v => RuleParam (v))
        ))
        .array
    );
  }
  auto rule1Params = [RuleValue (I32), RuleValue (I32)];
  auto example1 = ruleFrom (`first`, rule1Params);
  rules.addRule (&example1, rule1Params);
  testRule (rule1Params);
  auto rule2Params = rule1Params ~ [RuleValue (String)];
  auto example2 = ruleFrom (`second`, rule2Params);
  rules.addRule (&example2, rule2Params);
  testRule (rule2Params);
  testRule (rule1Params);
  auto rule3Params = [RuleValue (I64), RuleValue (I32)];
  auto example3 = ruleFrom (`third`, rule3Params);
  rules.addRule (&example3, rule3Params);
  testRule (rule1Params);
}
struct EndOfRule {}

struct Rules {
  SetOfRuleP [RuleValue] [] setsForPositions;

  auto addRule (Rule2 * toAdd, RuleValue [] ruleVals) {
    const rValLen = ruleVals.length;
    if (setsForPositions.length < rValLen + 1) {
      setsForPositions.length = rValLen + 1;
    }
    foreach (i, ruleVal; ruleVals) {
      setsForPositions [i][ruleVal][toAdd] = true;
    }
    setsForPositions [rValLen][eor][toAdd] = true;
  }
  
  private auto rulesMatching (alias OnSet)(in RuleValue ruleValue, size_t index) {

    OnSet (setsForPositions [index][ruleValue]);
    ruleValue.visit! (
      (EndOfRule eor) {}
      , (RTValue val) {
        foreach (generalType; val.type.visitTypeConvs ()) {
          const convValInSet
            = RuleValue (val.tryImplicitConversion (generalType))
              in setsForPositions [index];
          if (convValInSet) {
            OnSet (*convValInSet);
          }
        }
      }
      , (TypeId type) {
        foreach (generalType; type.visitTypeConvs ()) {
          const genValInSet = RuleValue (generalType) in setsForPositions [index];
          if (genValInSet) {
            OnSet (*genValInSet);
          }
        }
      }
    );
  }

  auto matchRule (in RuleValue [] ruleVals) {
    assert (ruleVals.length > 0);
    assert (ruleVals [$-1] == eor);
    const (Rule2) * [] matches;
    SetOfRuleP possibleMatches;
    // Fill possibleMatches.
    rulesMatching! ((s) {
      foreach (ruleP; s.keys) {
        possibleMatches [ruleP] = true;
      }
    }) (ruleVals [0], 0);

    foreach (i, ruleVal; ruleVals [1..$]) {
      //debug writeln (`POS `, i);
      // For next iteration.
      SetOfRuleP savedPossibleMatches;
      rulesMatching! ((setOfRules) {
        // TODO: Optimization: use the smallest set for the loop.
        foreach (ruleP; possibleMatches.keys) {
          if (ruleP in setOfRules) {
            savedPossibleMatches [ruleP] = true;
          }
        }
      }) (ruleVal, i + 1);
      
      // Also check for rule end.
      auto endingRulesAtPos = eor in setsForPositions [i + 1];
      if (endingRulesAtPos) {
        // Check in possible matches because savedPossibleMatches doesn't
        // know about the eoc.
        auto endFound = possibleMatches.keys.filter! (
          k => k in * endingRulesAtPos
        ).array;
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
    
    // Now let's check for specializations.
    if (matches.empty) {
      throw new Exception (`No rule found for ` ~ ruleVals.to!string);
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
                `Multuple rules match `, ruleVals, ":\n", bestMatch, '\n', alternative
              ));
            } else if (dir == firstToSecond) {
              specDir = alternativeIsSpec;
            } else if (dir == secondToFirst) {
              specDir = bestMatchIsSpec;
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


/+



struct PosWithVal {
  uint pos;
  RuleValue ruleValue;
}

struct FuncTree {
  // Ordered by pos.
  PosWithVal [] common;
  FuncTree [] specializations;
  // Null if just specializations have rules.
  Nullable!Rule2 rule;
  FuncTree * possibleParent;
  invariant {
    assert (rule._is!Rule2 || !specializations.empty);
  }
  bool matches (in RTValue [] values) {
    if (common.length > 0) {
      // First check that all positions fit in values
      if (common [$-1].pos >= values.length) {
        return false;
      }
    }
    foreach (ref commonVal; common) {
      auto valueAtC = values [commonVal.pos];
      if (! commonVal.ruleValue.visit! (
        (RTValue specificVal) {
          return valueAtC.type.isSubTypeOf (specificVal.type)
            && valueAtC.tryImplicitConversion (specificVal.type) == specificVal;
        }
        , (TypeId type) {
          return valueAtC.type.isSubTypeOf (type);
        }
      )) {
        return false;
      }
    }
    return true;
  }

  auto specializationsThatMatch (in RTValue [] values) {
    return specializations
      .filter! (s => s.matches (values))
      .map! (s => s.rule);
  }

  auto bestMatchingRule (in RTValue [] values) {
    if (this.matches (values)) {
      auto spec = specializationsThatMatch (values);
      if (spec.empty) {
        return this.rule;
      } else {
        auto matched = spec.front;
        spec.popFront ();
        if (spec.empty) {
          return matched;
        } else {
          import std.conv : to;
          throw new Exception (`Multiple rules match ` ~ values.to!string);
        }
      }
    } else {
      return Nullable!Rule2 (null);
    }
  }

  /// params must be ordered wrt position.
  auto addRule (PosWithVal [] params) {
    assert (!params.empty);
    auto common = this.common; // Don't iterate over the field common.

    alias MaybeRuleVal = Nullable!RuleValue;
    struct SpecWithDiff {
      uint pos;
      MaybeRuleVal common;
      RuleValue newV;
    }
    SpecWithDiff [] newSpecializations;

    struct SubSpecWithDiff {
      uint pos;
      RuleValue common;
      MaybeRuleVal newV;
    }
    SubSpecWithDiff [] newSubSpecializations;

    struct Incompatible {
      uint pos;
      RuleValue common;
      RuleValue newV;
    }
    Incompatible [] incompatibles;

    // First fill the newSpecializations, newSubSpecializations, incompatibles
    // arrays.
    while (true) {
      // If any of the two is empty, should stop iterating.
      if (params.empty) {
        if (!common.empty) {
          // More in already existing, add them as subspecializations.
          newSubSpecializations ~= common.map! (c => SubSpecWithDiff (
            c.pos, c.ruleValue, MaybeRuleVal (null)
          )).array;
        }
        break;
      } else if (common.empty) {
        // More in new rule, add them as specializations.
        newSpecializations ~= params.map! (p => SpecWithDiff (
          p.pos, MaybeRuleVal (null), p.ruleValue
        )).array;
        break;
      }
      auto paramV = params.front;
      auto commonV = common.front;
      auto paramPos = paramV.pos;
      auto commonPos = commonV.pos;
       if (paramPos < commonPos) {
        // There's a param in the new rule which isn't on existing, so it's an
        // specialization.
        newSpecializations ~= SpecWithDiff (
          paramPos, MaybeRuleVal (null), paramV.ruleValue
        );
        params.popFront ();
      } else if (paramPos > commonPos) {
        // There's a param in existing which isn't on the new rule, so it's a
        // subspecialization.
        newSubSpecializations ~= SubSpecWithDiff (
          commonPos, commonV.ruleValue, MaybeRuleVal (null)
        );
      } else {
        // paramV pos == commonV pos
        auto commonRV = commonV.ruleValue;
        auto paramRV = paramV.ruleValue;
        with (ImplicitConversionDirection) {
          final switch (implicitDir (commonRV, paramRV)){
            case noConversionPossible:
              incompatibles ~= Incompatible (commonPos, commonRV, paramRV);
              break;
            case firstToSecond:
              newSpecializations ~= SpecWithDiff (
                commonPos, MaybeRuleVal (commonRV), paramRV
              );
              break;
            case secondToFirst:
              newSubSpecializations ~= SubSpecWithDiff (
                commonPos, commonRV, MaybeRuleVal (paramRV)
              );
              break;
            case twoAreTheSame:
              // No need to add to any array.
              break;
          }
        }
        params.popFront ();
        common.popFront ();
      } 
    }
    debug writeln (`Specializations `, newSpecializations);
    debug writeln (`SubSpecializations `, newSubSpecializations);
    debug writeln (`Incompats `, incompatibles);
    import std.exception;
    enforce (! (
      incompatibles.empty
      && newSpecializations.empty
      && newSubSpecializations.empty
    ), `Tried adding rule with same args as existing one`);
    if (
      !incompatibles.empty
      || ((!newSpecializations.empty) && (!newSubSpecializations.empty))
    ) {
      // If there are incompatibilities or both specs and subspecs, the branch
      // should split.
      assert (0, `TODO: Split tree`);
    } else if (!newSubSpecializations.empty) {
      assert (0, `TODO: Add subspecialization`);
    } else {
      assert (0, `TODO: Add specialization`);
    }
  }
}

unittest {
  import execute;
  import intrinsics;
  auto exampleV = RTValue (I32, Var (5));
  implicitDir (
    RuleValue (exampleV), RuleValue (exampleV)
  ).writeln;
  FuncTree (
    [
      PosWithVal (0, RuleValue (exampleV))
    ]
    , [] // specs 
    , Nullable!Rule2 (Rule2 ())
    , null
  ).matches ([exampleV]).writeln ();
}+/
