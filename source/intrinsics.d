module intrinsics;

import std.algorithm;
import std.conv;
import std.range;
import execute;
debug import std.stdio;

TypeId Kind; // Just a Type of Type.
TypeId String;
TypeId Symbol;
TypeId I8;
TypeId I16;
TypeId I32;
TypeId I64;
TypeId F32;
TypeId F64;
TypeId NamedTypeT;
TypeId ExpressionT;
ParametrizedKind Array;
ParametrizedKind SumType;
ParametrizedKind Struct;
TypeId EmptyArray; // Not an instance of array, has special rules.
TypeId ArrayOfTypes;
// Note: To prevent forward refs, this uses void * (which is an Expression [] *)
TypeId ArrayOfExpressions;

RuleScope * globalRules;
ValueScope globalScope;

RTValue asSymbol (string name) {
  return RTValue (Symbol, Var (name));
}
struct TypeImplicitConversions {
  TypeId [] moreGeneral;

  private auto visitT (TypeId type) const {
    bool [TypeId] visitedTypes;
    auto typesToTry = [type];
    Appender! (TypeId []) toRet;
    while (!typesToTry.empty) {
      const t = typesToTry [$-1];
      typesToTry = typesToTry [0 .. $-1];
      toRet ~= t;
      const tInImplicit = t in implicitConversions;
      if (tInImplicit) {
        foreach (generalType; (* tInImplicit).moreGeneral) {
          visitedTypes.require (generalType, {
            typesToTry ~= generalType;
            return true;
          } ());
        }
      }
    }
    return toRet [];
  }
}

TypeImplicitConversions [TypeId] implicitConversions;

/// Includes itself and all the types this one can implicitly convert to.
auto visitTypeConvs (TypeId type) {
  auto tInImplicit = type in implicitConversions;
  if (tInImplicit) {
    return (*tInImplicit).visitT (type);
  }
  return [type];
}

private TypeId addPrimitive (string name) {
  // As of now, all variables will be stored on a Var, so that'll be the size.
  return globalScope.addType (name, Var.sizeof).get!TypeId;
}

shared static this () {
  // Primitives:
  Kind = addPrimitive (`Kind`);
  String = addPrimitive (`String`);
  Symbol = addPrimitive (`Symbol`);
  I8 = addPrimitive (`I8`);
  I16 = addPrimitive (`I16`);
  I32 = addPrimitive (`I32`);
  I64 = addPrimitive (`I64`);
  F32 = addPrimitive (`F32`);
  F64 = addPrimitive (`F64`);
  NamedTypeT = addPrimitive (`NamedType`);
  ExpressionT = addPrimitive (`Expression`);
  EmptyArray = addPrimitive (`EmptyArray`);

  // Implicit conversions:
  implicitConversions [F32] = TypeImplicitConversions ([F64]);
  implicitConversions [I32] = TypeImplicitConversions ([F64, I64]);
  implicitConversions [I16] = TypeImplicitConversions ([F32, I32]);
  implicitConversions [I8] = TypeImplicitConversions ([I16]);

  // Parametrized types:
  Array = ParametrizedKind (
    `Array`, [Kind]
  );
  ArrayOfTypes = arrayOf (Kind);
  // Array of types should be here too?
  SumType = ParametrizedKind (
    `SumType`, [ArrayOfTypes]
  );
  Struct = ParametrizedKind (
    `Struct`, [ArrayOfTypes]
  );
  auto SymbolOrNamedType = sumTypeOf (
    [typeToRTValue (Symbol), typeToRTValue (NamedTypeT)]
  );
  auto ArrayOfSymbolOrNamedType = arrayOf (SymbolOrNamedType);
  ArrayOfExpressions = arrayOf (ExpressionT);

  import std.functional : toDelegate;
  globalRules = new RuleScope ([
    // I32 plus I32
    fromD!plus (automaticParams!plus (1))
    , fromD!writeString (automaticParams!writeString (0, `writeln`))
    , Rule ( // apply Expression []
      [
        RuleParam (I32)
        , RuleParam (`apply`.asSymbol ())
        , RuleParam (ArrayOfExpressions)
      ]
      , (
        in RTValue [] args
        , ref RuleMatcher ruleTree
      ) {
        assert (args.length == 3);
        /+debug writeln (
          "Apply called, will now execute with:\n\t"
          , args [0].value, ` in `, args [1].value
        );+/
        import parser : Expression;
        auto result = executeFromExpressions (
          args [2].value.get! (Expressions).expressions
          , [args [0]]
          , ruleTree
          , globalScope
        );
        if (result._is!UserError) {
          throw new Exception (result.get!UserError.message);
        }
        //debug writeln (`Apply result: `, result);
        return result.get!RTValue;
      }.toDelegate
    )
    , Rule ( // Symbol | NamedType [] Expression [] // TODO: Change to new syntax
      [RuleParam (ArrayOfSymbolOrNamedType), RuleParam (ArrayOfExpressions)]
      , (
        in RTValue [] args
        , ref RuleMatcher ruleTree
      ) {
        assert (args.length == 2);
        debug writeln (`TODO: Declare a function. Called with `, args);
        return RTValue (I32, Var (555));
      }
    )
  ]);
}

extern (C) {
  int plus (int a, int b) { return a + b; }
  string writeString (string toWrite) {
    import std.stdio;
    writeln (toWrite);
    return toWrite;
  }
}

template TypeMapping (DType) {
  static if (is (DType == string)) {
    alias TypeMapping = String;
  } else static if (is (DType == int)) {
    alias TypeMapping = I32;
  } else static if (is (DType == float)) {
    alias TypeMapping = F32;
  } else static if (is (DType == AsValueListRet)) {
    alias TypeMapping = Function;
  }
}

import std.traits;
import rulematcher;
RuleParam [] automaticParams (alias Fun)(
  size_t nameLocation = 0
  , string name = Fun.mangleof
) {
  alias DParams = Parameters!Fun;
  RuleParam [] params;
  foreach (Param; DParams) {
    params ~= RuleParam (TypeMapping!Param);
  }
  return params [0 .. nameLocation]
    ~ RuleParam (RTValue (Symbol, Var (name)))
    ~ params [nameLocation .. $];
}

import std.conv : to, text;
Rule fromD (alias Fun) (RuleParam [] params = automaticParams!Fun) {
  alias RetType = ReturnType!Fun;
  alias Params = Parameters!Fun;
  return Rule (params, (
    in RTValue [] args
    , ref RuleMatcher ruleTree
  ) {
      uint lastIdx = 0;
      // TODO: Foreach with mixin that sets all the values from args.
      static foreach (i, Param; Params) {
        while (args [lastIdx].type == Symbol) {
          lastIdx ++;
        }
        /+
        auto expectedType = TypeMapping!Param;
        assert (
          args [i].type == expectedType
          , text (`Expected arg `, i, ` of `, FunName, ` to be of type `, expectedType.name)
        );
        +/
        mixin (q{auto arg} ~ i.to!string ~ q{ = args [lastIdx].value.get!Param ();});
        lastIdx ++;
      }
      mixin (
        q{auto result = Fun (}
          ~ iota (Params.length)
          .map!(`"arg" ~ a.to!string`)
          .joiner (`, `)
          .to!string 
        ~ q{);}
      );
      return RTValue (TypeMapping!RetType, Var (result));
    }
  );
}

/+
alias MaybeValue = Nullable!Var;

struct OrderedValuedParam {
  uint position;
  RTValue value;
}
struct OrderedValuedParams {
  OrderedValuedParam [] params;
  ApplyFun apply;
}
struct NoMatch {}

alias MaybeApplyFun = Variant! (ApplyFunContainer, NoMatch, UserError);

struct PatternTree {
  /// Params that need to be satisfied to match this pattern.
  OrderedValuedParams common;
  /// They musn't repeat an ancestor position as they are implicit to be the same.
  /// They also shouldn't have 0 params, only the root can have no params.
  PatternTree [] moreSpecificPatterns;

  /// Constructor for just common parameters.
  this (OrderedValuedParams common) {
    this.common = common;
    this.moreSpecificPatterns = [];
  }
  /// Constructor for common and specific parameters.
  this (OrderedValuedParams common, PatternTree [] moreSpecificPatterns) {
    this.common = common;
    this.moreSpecificPatterns = moreSpecificPatterns;
  }

  MaybeApplyFun bestMatchFor (in RTValue [] inputs) {
    if (! common.params.all! (c => inputs [c.position] == c.value)) {
      return MaybeApplyFun (NoMatch ());
    }
    auto bestMatches = moreSpecificPatterns
      .map! (sp => sp.bestMatchFor (inputs));
    auto err = bestMatches.save ().find! (sp => sp._is!UserError);
    if (!err.empty) {
      return err.front;
    }
    auto bestFound = bestMatches.filter! (sp => !sp._is!ApplyFunContainer);
    if (bestFound.empty) {
      // No specific branch matched, but this general one did, so return this
      // one's apply.
      return MaybeApplyFun (ApplyFunContainer (common.apply));
    } else {
      // There's at least one more specific match.
      // It must be exactly one to avoid ambiguity.
      auto best = bestFound.front;
      moreSpecificPatterns.popFront ();
      if (moreSpecificPatterns.empty) {
        return MaybeApplyFun (best.get!ApplyFunContainer);
      } else {
        return MaybeApplyFun (UserError (`Multiple patterns match `, inputs));
      }
    }
  }
}

alias ScopeRule = RuleTree; // Weak reference
  
// Pointer because of structure self-reference.
// alias Branch = Variant! (RuleTree *, Rule);

alias BranchingParam = Variant! (TypeId, string, typeof (null));

private alias ParentTreeRef = Nullable! (RuleTree *);
private alias Branches = RuleTree * [BranchingParam];
private alias BranchesOrRule = Variant! (Rule, Branches);
const nullBP = BranchingParam (null);

BranchingParam toBP (TypeOrSymbol tS) {
  return tS.visit! ((a) => BranchingParam (a));
}
/// An easily searchable tree structure to match Expressions with Rules.
/// Currently implemented as a radix tree.
struct RuleTree {
  
  @disable this ();
  /// Must have at least one rule.
  this (Rule [] rules) {
    assert (rules.length > 0);
    this.commonParams = rules.front.args;
    this.following = BranchesOrRule (rules.front);
    this.parent = null;
    foreach (rule; rules [1 .. $]) {
      this.addRule (rule);
    }
  }

  private this (
    TypeOrSymbol [] commonParams, BranchesOrRule following, ParentTreeRef parent
  ) {
    this.commonParams = commonParams;
    this.following = following;
    this.parent = parent;
  }

  TypeOrSymbol [] commonParams;
  /// Key is the first param in the rule that isn't in the others.
  /// Null if no different parameters (eg. a rule might start the same as others
  /// but the other ones have extra parameters).

  BranchesOrRule following;
  ParentTreeRef parent;

  // Note: Currently the following is allowed to change from Rule to branches.
  // If that becomes disallowed, no matching is needed to delete nodes from the
  // scope. BUT AS OF NOW THAT ISN'T THE CASE, on split, the leaf node might
  // become a branch.
  /// Adds a new rule to the tree and returns its containing leaf
  /// (which might mutate on further RuleTree method calls)
  RuleTree * addRule (Rule rule, size_t ruleArgStartIndex = 0) {
    auto rArgs = rule.args [ruleArgStartIndex .. $];
    // zip -> countUntil didn't seem to work, so manual loop is used
    const commonLen = this.commonParams.length;
    const rArgsLen = rArgs.length;
    size_t branchingPos = 0;
    for (
      ; commonLen > branchingPos
        && rArgsLen > branchingPos
        && rArgs.ptr [branchingPos] == commonParams.ptr [branchingPos]
      ; branchingPos ++
    ) {}
    assert (branchingPos <= commonLen);
    assert (branchingPos <= rArgsLen);

    Tuple!(BranchingParam, TypeOrSymbol []) newBranch (TypeOrSymbol [] rules) {
      auto branchingKey = BranchingParam (null);
      TypeOrSymbol [] subTreeCommon;
      if (rules.length > branchingPos) {
        // There are more params in the rule. Use the first one as key.
        branchingKey = BranchingParam (rules [branchingPos]);
        subTreeCommon = rules [branchingPos + 1 .. $];
      }
      return tuple (branchingKey, subTreeCommon);
    }

    auto splitFollowing () {
      auto chopped = newBranch (this.commonParams);
      auto subTreeA = newBranch (rArgs);
      auto subTree = new RuleTree (
        subTreeA [1], BranchesOrRule (rule), ParentTreeRef (&this)
      );

      // Branches before consumming all the this.common params.
      // So must split this tree at that point into the rest of this one
      // and another with the new rule.
      this.following = BranchesOrRule ([
        chopped [0] : new RuleTree (
          chopped [1], this.following, ParentTreeRef (&this)
        )
        , subTreeA [0] : subTree
      ]);
      return subTree;
    }

    if (commonLen == branchingPos) {
      // Keep the current splitting point.
      return following.visit! (
        (Rule currentRule) {
          enforce (rArgsLen != commonLen, text (
            `Rule `, rule
            , ` has same parameters as existing one: `, currentRule
          ));
          // rArgsLen > commonLen
          return splitFollowing ();
        }
        , (ref Branches branches) {
          bool rArgsIsBPos = rArgsLen == branchingPos;
          auto commonStart = branchingPos + (rArgsIsBPos ? 0 : 1);
          RuleTree * toRet = (&this);
          // See https://dlang.org/spec/hash-map.html#advanced_updating
          branches.update (
            rArgsIsBPos ? nullBP : BranchingParam (rArgs [branchingPos])
            , {
              toRet = new RuleTree (
                rArgsIsBPos ? [] : rArgs [commonStart .. $]
                , BranchesOrRule (rule)
                , ParentTreeRef (&this)
              );
              return toRet;
            }, (ref RuleTree * t) {
              t.addRule (rule, ruleArgStartIndex + commonStart);
              return t;
            }
          );
          return toRet;
        }
      );
    } else {
      auto toRet = splitFollowing ();
      // Create new splitting point.
      this.commonParams = this.commonParams [0 .. branchingPos];
      return toRet;
    }
  }

  alias MatchRet = Nullable!MatchWithPos;
  private auto withOffset (MatchRet mR, size_t offset) {
    return mR.visit! (
      (typeof (null)) => MatchRet (null)
      , (MatchWithPos mwp) => MatchRet (mwp.rule, mwp.position + offset)
    );
  }

  enum nullRule = MatchRet (null);
  /// Checks if the beginning of ruleArgs matches any rule stored in this tree
  /// and returns it.
  /// If there are multiple rules that match, the longest one is given priority.
  /// Note that a match might not be of the entire ruleArgs.
  /// null is returned if no rule matches
  MatchRet matchRule (in TypeOrSymbol [] ruleArgs) {
    foreach (i, ruleArg; ruleArgs) {
      if (commonParams.length == i) {
        // We still have more ruleArgs.
        // We will use the longest match that we find.
        // Note that the ruleArgs correspond to 1+ expressions, this algorithm
        // just checks the first one.
        return this.following.visit! (
          (Rule r) {
            return MatchRet (MatchWithPos (r, commonParams.length));
          }
          , (ref Branches branches) {
            auto subT = BranchingParam (ruleArg) in branches;
            if (subT) {
              auto subTResult = (*subT).matchRule (ruleArgs [i + 1 .. $]);
              if (!subTResult.isNull ()) {
                auto mwp = subTResult.get!MatchWithPos;
                mwp.position += commonParams.length + 1;
                return MatchRet (mwp);
              }
            }
            auto nullT = nullBP in branches;
            if (nullT) {
              return withOffset ((*nullT).matchRule ([]), commonParams.length);
            }
            return nullRule;
          }
        );
      }
      if (ruleArg != this.commonParams [i]) {
        // Different arg to what rule expected, return no match.
        return nullRule;
      }
    }
    if (ruleArgs.length == commonParams.length) {
      // Args matched this tree.
      // So either, this tree has the rule or we search the null branch.
      return this.following.visit! (
        (Rule r) => MatchRet (r, commonParams.length) // Exact match
        , (Branches branches) {
          auto nullT = nullBP in branches;
          if (nullT) {
            // Also exact match if successful.
            // The branch might have more common params which triggers an error.
            return withOffset ((*nullT).matchRule ([]), commonParams.length);
          }
          return nullRule;
        }
      );
    }
    return nullRule;
  }

  /// Removes rule from this tree.
  /// Assumes that the rule exists. DOESN'T CHECK FOR IT.
  void removeRule (TypeOrSymbol [] ruleArgs) {
    assert (this.following._is!Branches);
    auto branches = this.following.get!Branches;
    // debug writeln (`Branches before: `, branches);
    assert (
      branches.length >= 2
      , `Shouldn't have single branch before prunning`
    );

    auto commonLen = this.commonParams.length;
    void recurse (RuleMatcher * subT, BranchingParam bp) {
      if (subT.following._is!Rule) {
        // Found the rule, remove the branch with it.
        branches.remove (bp);
        if (branches.length == 1) {
          // We don't want trees with single branches.
          // Merge with that sub-branch.
          auto singleC = branches.byKeyValue ().front ();
          this.commonParams ~= singleC.key.visit! (
            (typeof (null)) => TypeOrSymbol [].init
            , (a) => [TypeOrSymbol (a)]
          ) ~ singleC.value.commonParams;
          this.following = singleC.value.following;
          // debug writeln (`Merged with only child `, singleC);
          // debug writeln (`Now follows `, following);
        }
      } else {
        const firstSubP = commonLen + (bp == nullBP ? 0 : 1);
        subT.removeRule (ruleArgs [firstSubP .. $]);
      }
    }

    auto rArgLen = ruleArgs.length;
    if (rArgLen > commonLen) {
      auto bp = BranchingParam (ruleArgs [commonLen]);
      auto subT = bp in branches;
      if (subT) {
        recurse (*subT, bp);
        return;
      }
    }
    // Didn't find on ruleArgs [commonLen], so it must be in null
    auto nullInB = nullBP in branches;
    assert (nullInB);
    recurse (*nullInB, nullBP);
  }

  /// Uses a multi-line indented approach.
  void toString (
    scope void delegate (const (char)[]) sink
    , uint tabsBefore = 0
  ) {
    auto tabSinks = '\t'.repeat (tabsBefore).array;
    void sinkT (string s) {
      sink (tabSinks);
      sink (s);
    }
    sink ("RuleMatcher {\n");
    sinkT ("C: [");
    foreach (commonParam; commonParams) {
      sink (commonParam.toString);
      sink (", ");
    }
    sink ("]\n");
    sinkT ("B:\n");
    following.visit!(
      (Rule r) {
        sinkT ("\t");
        sink (r.args.to!string);
      }
      , (Branches b) {
        foreach (a; b.byKeyValue) {
          sinkT ("\t");
          sink (a.key.toString);
          sink (": ");
          (*a.value).toString (sink, tabsBefore + 1);
          sink ("\n");
        }
      }
    );
    sink ("\n");
    sinkT ("}");
  }
}

unittest {
  auto ruleScope = RuleScope ([]);
  auto justErr = delegate (
    in RTValue [] apply
    , ref RuleMatcher ruleTree
  ) {
    return RTValue (I8, Var (255));
  };

  auto rArgs = [TypeOrSymbol (`Example`), TypeOrSymbol (`rule`)];
  auto rule = Rule (rArgs, justErr);
  auto tree = RuleMatcher ([rule]);

  // Test splitting at bigger pos:
  auto biggerRArgs = rArgs ~ TypeOrSymbol (I32);
  auto biggerRule = Rule (biggerRArgs, justErr);
  // Matches the first part.
  assert (tree.matchRule (biggerRArgs).get!MatchWithPos.rule == rule);
  tree.addRule (biggerRule);
  assert (tree.matchRule (biggerRArgs).get!MatchWithPos.rule == biggerRule);
  auto smallerRule = Rule (rArgs [0..1], justErr);
  tree.addRule (smallerRule);
  assert (tree.matchRule (rArgs [0..1]).get!MatchWithPos.rule == smallerRule);
  assert (tree.matchRule (rArgs).get!MatchWithPos.rule == rule);
  assert (tree.matchRule (biggerRArgs).get!MatchWithPos.rule == biggerRule);
  tree.removeRule (biggerRArgs);
  // Assert not there anymore.
  assert (tree.matchRule (biggerRArgs).get!MatchWithPos.rule == rule);
  // Test with different args.
  auto differentRArgs = [TypeOrSymbol (`Hello`), TypeOrSymbol (`There`)];
  auto differentRule = Rule (differentRArgs, justErr);
  tree.addRule (differentRule);
  assert (tree.matchRule (differentRArgs).get!MatchWithPos.rule == differentRule);
  tree.removeRule (differentRArgs);
  assert (tree.matchRule (differentRArgs).isNull ());
}
+/
