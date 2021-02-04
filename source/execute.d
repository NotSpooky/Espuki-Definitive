import mir.algebraic;
import std.conv : text, to;
import std.exception : enforce;
import std.typecons : Tuple, tuple;
import parser : Expression, ExpressionArg, SumTypeArgs, ArrayArgs;

/// An error in the code that the compiler/interpreter should show.
struct UserError {
  string message;
  this (T ...)(T args) {
    this.message = text (args);
  }
}

/// Used to create parametrized types.
struct ParametrizedKind {
  TypeId [] argTypes;
  string baseName;
  TypeId [RTValue []] instances;
  this (string baseName, TypeId [] argTypes) {
    this.baseName = baseName;
    this.argTypes = argTypes;
  }

  TypeId instance (const RTValue [] args, TypeInfo_ delegate () createTypeInfo) {
    // First check whether this has already been instanced.
    auto inInstances = args in instances;
    if (inInstances) {
      // Yes, return it.
      return *inInstances;
    } else {
      // No, create the new instance.
      const toRet = globalTypeInfo.length;
      globalTypeInfo ~= createTypeInfo ();
      instances [args] = toRet;
      return toRet;
    }
  }

  TypeId instance (const RTValue [] args, size_t size) {
    // Args should have the Kind's expected types.
    if (
      zip (StoppingPolicy.requireSameLength, args.map!`a.type`, argTypes)
        .all! (a => a [0].isSubTypeOf (a [1]))
    ) {
      // Types match.
      return instance (args, () => new ParametrizedTypeInfo (
        &this
        , args
        , size //args.map! (a => globalTypeInfo [a.value.get!TypeId].size).sum
      ));
    } else {
      throw new Exception (text (
        `Arguments `, args, ` don't match ` ~ baseName, `'s params: `, argTypes
      ));
    }
  }
}

// Note: Verbose name because TypeId == long.
RTValue typeToRTValue (TypeId type) {
  return RTValue (Kind, Var (type));
}

TypeId arrayOf (TypeId elementType) {
  const asRTVals = [typeToRTValue (elementType)];
  return Array.instance (asRTVals, () => new ArrayTypeInfo (elementType));
}

TypeId sumTypeOf (RTValue [] typeIds) {
  import std.exception : enforce; 
  return SumType.instance (typeIds, () => new ParametrizedTypeInfo (
    &SumType
    , typeIds
    , uint.sizeof /* As of now, current type will be stored on UI32 */
      + typeIds
        // TODO: Use correct type of exception.
        .tee! (t => enforce (t.type == Kind, `Non-type used for sumtype creation`))
        .map! (t => globalTypeInfo [t.value.get!TypeId].size)
        .maxElement
  ));
}

TypeId structTypeOf (RTValue [] members) {
  return Struct.instance (members, () => new StructTypeInfo (members));
}

class TypeInfo_ {
  const size_t size;
  this (size_t size) {
    this.size = size;
  }
}

class PrimitiveTypeInfo  : TypeInfo_ {
  string name;
  this (string name, size_t size) {
    super (size);
    this.name = name;
  }
  override string toString () {
    return name;
  }
}

class ParametrizedTypeInfo : TypeInfo_ {
  const ParametrizedKind * kind;
  const RTValue [] args;
  this (ParametrizedKind * kind, const RTValue [] args, size_t size) {
    assert (kind !is null);
    super (size);
    this.kind = kind;
    this.args = args;
  }
  override string toString () {
    return kind.baseName ~ ` (` ~
      args.map! (a => a.value.visit! (b => b.to!string))
        .joiner (`, `)
        .to!string
    ~ `)`;
  }
}

class ArrayTypeInfo : ParametrizedTypeInfo {
  const size_t elementSize; // Just a cache, coulf be calculated automatically.
  this (const TypeId elementType) {
    super (
      &Array
      , [RTValue (Kind, Var (elementType))]
      , (void *).sizeof + size_t.sizeof
    );
    this.elementSize = globalTypeInfo [elementType].size;
  }
  override string toString () {
    return globalTypeInfo [args [0].value.get!TypeId].toString () ~ ` []`;
  }
}

class StructTypeInfo : ParametrizedTypeInfo {
  size_t [string] offsets;
  this (const RTValue [] members) {
    auto totalSize = 0;
    foreach (member; members) {
      enforce (member.type == NamedTypeT);
      auto namedType = member.value.get!NamedType;
      const memberS = globalTypeInfo [namedType.type].size;
      offsets [namedType.name] = totalSize;
      totalSize += size;
    }
    super (
      &Struct
      , members
      , (void *).sizeof /+ Structs will store a void * for now  +//+totalSize+/
    );
  }
}

TypeInfo_ [] globalTypeInfo;

/// As of now just handles type equality by id.
bool isSubTypeOf (TypeId type, TypeId parent) {
  if (type == parent) {
    return true;
  }
  // TODO: Implicit conversions here.
  // Such as Type -> SumType including it
  // Ix to Iy with y > x
  // etc
  return false;
}

RTValue tryImplicitConversion (ref RTValue val, TypeId objective) {
  if (val.type.isSubTypeOf (objective)) {
    return val;
  } else {
    throw new Exception (
      text (val, ` canot be converted to `, globalTypeInfo [objective])
    );
  }
}

alias ApplyFun = RTValueOrErr delegate (
  in RTValue [] inputs
  , ref RuleTree ruleTree
);
/// mir.algebraic.Variant seems to have trouble with ApplyFun so we wrap it.
struct ApplyFunContainer {
  ApplyFun applyFun;
}

alias TypeId = size_t;
struct NamedType {
  string name;
  TypeId type;
}

struct StructType {
  size_t [TypeId] offsets;
  @disable this ();
  this (TypeId [] memberTypes) {
    
  }
}

// For avoiding circular structures in Var without using the This type several
// layers below.
struct Expressions {
  private void * ptr;
  this (Expression [] * ptr) {
    assert (ptr !is null);
    this.ptr = ptr;
  }
  auto expressions () const {
    return *(cast (Expression [] *) ptr);
  }
}
alias Var = Variant! (
  float
  , string
  , int
  , TypeId
  , NamedType
  , NamedType []
  , This [] // For arrays and structs.
  , typeof (null)
  , Expressions /* is Expression [] * */
  , StructType
);

/// A value in the interpreter.
struct RTValue {
  TypeId type;
  Var value;
  this (TypeId type, Var value) {
    this.type = type;
    this.value = value;
  }

  void toString (
    scope void delegate (const (char)[]) sink
  ) const {
    sink (globalTypeInfo [this.type].toString ());
    sink (` `);
    if (value._is!(Var [])) {
      sink (`[`);
      sink (
        value.get! (Var [])
          .map! (v => v.visit! (a => a.to!string ()))
          .joiner (`, `)
          .to!string
      );
      sink (`]`);
    } else {
      sink (value.visit! (a => a.to!string ()));
    }
  }
}

alias TypeOrErr = Variant! (TypeId, UserError);

struct ValueScope {
  RTValue [string] values;
  TypeOrErr addType (string identifier, size_t size) {
    auto toRet = TypeOrErr (UserError (
      `Type ` ~ identifier ~ ` already exists in the scope`)
    );
    this.values.require (
      identifier
      , {
        const typeId = globalTypeInfo.length;
        globalTypeInfo ~= new PrimitiveTypeInfo (identifier, size);
        toRet = TypeOrErr (typeId);
        return RTValue (Kind, Var(typeId));
      } ()
    );
    return toRet;
  }
}

import std.typecons : Tuple;
alias InputParam = Tuple! (string, `name`, uint, `index`);
struct RTFunction {
  InputParam [] inputNames;
  Expression [] expressions;
  /+
  // Mir seemed to have trouble calculating this struct's hash.
  size_t toHash () const nothrow {
    return expressions.hashOf (inputNames.hashOf);
  }+/
}

auto apply (RTFunction fun, RTValue [] args) {
  RTValue [string] identifierScope;
  assert (fun.inputNames.length == args.length);
  foreach (i, arg; args) {
    identifierScope [fun.inputNames [i].name] = arg;
  }
  
}

alias RTValueOrErr = Variant! (RTValue, UserError);

alias TypeOrSymbol = Variant! (TypeId, string);
// Could simply add the strings as RTValues of symbols instead.
alias RTValueOrSymbol = Variant! (RTValue, string);
struct MatchWithPos {
    Rule rule;
    size_t position;
    this (Rule rule, size_t position) {
      this.rule = rule;
      this.position = position;
    }
  }

/// Finds and applies matches until the args/params are exhausted.
RTValueOrErr lastMatchResult (
  ref RuleTree ruleTree
  , in TypeOrSymbol [] params
  , in RTValueOrSymbol [] args) {
  assert (params.length == args.length);

  return ruleTree.matchRule (params).visit! (
    // No rule matches.
    (typeof (null)) => RTValueOrErr (
      UserError (`Couldn't match rule for `, args)
    ), (MatchWithPos mwp) {
      // There's a match and it ends at mwp.position.
      // Apply the rule corresponding to the found match.
      auto matchResultVal = mwp.rule.apply (
        args
          .filter! (a => a._is!RTValue)
          .map! (a => a.get!RTValue)
          .array
        , ruleTree
      );
      //auto matchResultVal = RTValueOrErr (owo);
      return matchResultVal.visit! (
        // If errored, just pass it.
        (UserError ue) => matchResultVal
        , (RTValue val) {
          // Else, this value becomes the first argument for the next match.
          const cutPoint = mwp.position;
          if (cutPoint == args.length) {
            // Finished matching all the args.
            return matchResultVal;
          } else {
            // Still more to match, we add the current result as first arg/param
            // Could be made faster if we avoid concatenation.
            return lastMatchResult (
              ruleTree
              , [TypeOrSymbol (val.type)] ~ params [cutPoint .. $]
              , [RTValueOrSymbol (val)] ~ args [cutPoint .. $]
            );
          }
        }
      );
    }
  );
}

RTValue subValue (
  const ExpressionArg [] args
  , ref RuleTree ruleTree
  , ref ValueScope scope_
) {
  auto result = executeFromExpression (
    Expression (args, Nullable!string (null))
    , [] // Last result isn't sent to subexpressions.
    , ruleTree
    , scope_
  );
  if (result._is!UserError) {
    throw new Exception (
      `Error getting subExpression result: `
        ~ result.get!UserError.message
    );
  } else {
    return result.get!RTValue;
  }
}

auto subValues (
  const ExpressionArg [][] args
  , ref RuleTree ruleTree
  , ref ValueScope scope_
) {
  return args.map! (eA => subValue (eA, ruleTree, scope_));
}

RTValue createArray (
  const ExpressionArg [][] args
  , ref RuleTree ruleTree
  , ref ValueScope scope_
) {
  if (args.empty) {
    return RTValue (EmptyArray, Var (null));
  }
  auto subVs = subValues (args, ruleTree, scope_);
  const elType = subVs.front.type;
  auto retType = arrayOf (elType);
  Var [] afterConversionArray = subVs
    .map! (s => s.tryImplicitConversion (elType).value)
    .array;
  return RTValue (retType, Var (afterConversionArray));
}

void addSumTypeMethods (
  ref RuleTree
  , RTValue sumTypeType
  , TypeId [] sumTypeTypes // Member types.
) {
  debug writeln (`TODO: Add sumtype methods`);
  /+
  // TODO: Consider scope.
  ruleTree.addRule (
    Rule (
      [
        TypeOrSymbol (I32) // = sumTypeType, not Kind
        , TypeOrSymbol (ArrayOfExpressions)] // Instance of each of sumTypeTypes
      , (
        in RTValue [] args
        , ref RuleTree ruleTree
      ) {
        assert (args.length == 2);
        /+debug writeln (
          "Apply called, will now execute with:\n\t"
          , args [0].value, ` in `, args [1].value
        );+/
        import parser : Expression;
        auto result = executeFromExpressions (
          args [1].value.get! (Expressions).expressions
          , [args [0]]
          , ruleTree
          , globalScope
        );
        //debug writeln (`Apply result: `, result);
        return result;
      }
    )
  );
  +/
}

RTValue createSumType (
  const ExpressionArg [][] args
  , ref RuleTree ruleTree
  , ref ValueScope scope_
) {
  // First arg is the added type, second either a normal type or a sumtype.
  debug writeln (`Args for sumtype: `, args);
  auto subVs = subValues (args, ruleTree, scope_).array;
  debug writeln (`Types in sumtype `, subVs.map!(s => s.value.get!TypeId));
  assert (!subVs.empty);
  auto toRet = sumTypeOf (subVs);
  foreach (const subV; subVs) {
      (const RTValue subV) {
      ruleTree.addRule (Rule (
        // TODO: Match this sumtype specifically instead of any kind.
        [TypeOrSymbol (Kind), TypeOrSymbol (subV.value.get!TypeId)]
        , (
          in RTValue [] rArgs
          , ref RuleTree ruleTree
        ) {
          debug writeln (`Instanced `, globalTypeInfo [toRet].toString, ` with `, subV.value.get!TypeId);
          assert (rArgs.length == 2);
          return RTValueOrErr (RTValue (subV.value.get!TypeId, rArgs [1].value));
        }
      )); 
    } (subV);
  }
  return typeToRTValue (toRet);
}
/// Finds appropriate rules to match the expression and returns the result
/// of applying those rules to the match.
/// If the best match doesn't comprise the full expression, it's result is given
/// as the first argument for another match.
/// This process is repeated until the expression is exhausted or an error occurs.
RTValueOrErr executeFromExpression (
  in Expression expression
  , in RTValue [] lastResult
  , ref RuleTree ruleTree
  , ref ValueScope scope_
) {
  assert (
    lastResult.length <= 1
    , `TODO: Implement multiple return values to tuple conversion`
  );
  assert (expression.args.length > 0, `Lexer shouldn't send empty expressions`);
  const useImplicitFirstArg
    = !expression.usesUnderscore && lastResult.length > 0;
  auto args = (useImplicitFirstArg ? [
    RTValueOrSymbol (lastResult [0])
  ] : []) ~ expression.args.map! (a =>
    a.visit! (
      (const Expression * subExpr) {
        auto subExprRet = executeFromExpression (
          *subExpr, lastResult, ruleTree, scope_
        );
        if (subExprRet._is!RTValue) {
          auto result = subExprRet.get!RTValue;
          return RTValueOrSymbol (result);
        } else {
          throw new Exception (subExprRet.get!UserError.message);
        }
      }
      // Already a value, nothing to do.
      , (RTValue val) => RTValueOrSymbol (val)
      , (string a) {
        // If the string is an identifier in the scope, use that value,
        // else treat is as a symbol.
        auto inScope = a in scope_.values;
        if (inScope) {
          return RTValueOrSymbol (*inScope);
        }
        return RTValueOrSymbol (a);
      }
      , (const ArrayArgs!ExpressionArg arrayElementExpressions)
        => RTValueOrSymbol (createArray (
          arrayElementExpressions.args
          , ruleTree
          , scope_
        ))
      , (const ExpressionArg [] subExpression)
        => RTValueOrSymbol (subValue (subExpression, ruleTree, scope_))
      , (const SumTypeArgs!ExpressionArg sumTypeArgs) 
        => RTValueOrSymbol (createSumType (sumTypeArgs.args, ruleTree, scope_))
    )
  ).array;
  if (args.length == 1 && args [0]._is!RTValue) {
    return RTValueOrErr (args [0].get!RTValue);
  }
  debug writeln (`Got as last result `, lastResult.map! (a => a.to!string));
  debug writeln (`Got as args `, args.map! (a => a.visit! (b => b.to!string)));
  auto params = args.map! (a => a.visit! (
    (RTValue val) => val.type
    , (string symbol) => symbol
  )).array;

  // debug writeln (`Args: `, args);
  // debug writeln (`Params: `, params);

  return lastMatchResult (ruleTree, params, args);
}

/// Chains multiple expressions together and returns the last one's return value
/// Can return UserError on error.
RTValueOrErr executeFromExpressions (
  in Expression [] expressions
  , RTValue [] lastResult
  , ref RuleTree ruleTree
  , ref ValueScope scope_
) {
  /+
  if (expressions.length == 0) {
    assert (lastResult.length == 1);
    return RTValueOrErr (lastResult [0]);
  }+/
  foreach (expression; expressions) {
    auto result = executeFromExpression (
      expression, lastResult, ruleTree, scope_
    );
    if (result._is!UserError) {
      return result;
    } else {
      // debug writeln (`res: `, result.get!RTValue.value.visit! (a => a.to!string));
      lastResult = [result.get!RTValue];
    }
  }
  // TODO: Allow returning multiple values.
  return RTValueOrErr (lastResult [0]);
}

debug import std.stdio;
import std.range;
RTValueOrErr executeFromLines (R)(R lines) if (is (ElementType!R == string)) {
  import lexer : asExpressions;
  import intrinsics : globalScope, globalRules;
  auto ruleTree = RuleTree (globalRules.rules);
  return asExpressions (lines, globalScope).visit! (
    (Expression [] expressions) { 
      return executeFromExpressions (expressions, [], ruleTree, globalScope);
    }
    , (UserError ue) {
      stderr.writeln (`Error: `, ue.message);
      return RTValueOrErr (ue);
    }
  );
}

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

size_t amountThatAreType (R)(R args) {
  return args.filter ! (arg => arg._is!Type).count ();
}

struct Rule {
  @disable this ();
  TypeOrSymbol [] args;
  PatternTree patternTree;
  /// Version for just matching by type.
  this (TypeOrSymbol [] args, ApplyFun apply) {
    assert (args.length > 0, `Rule with no args`);
    this.args = args;
    this.patternTree = PatternTree (OrderedValuedParams ([], apply));
  }

  /// Executes the most fitting pattern in patterns and returns its result.
  /// If no pattern fits, an UserError is returned.
  /// THIS DOESN'T DO THE MATCHING IN THE TREE.
  /// Check out the RuleTree.matchRule for that.
  RTValueOrErr apply (in RTValue [] inputs, ref RuleTree ruleTree) {
    auto fitting = this.patternTree.bestMatchFor (inputs);
    return fitting.visit! (
      (NoMatch nm) => RTValueOrErr (UserError (`No rule matches `, inputs))
      , (ApplyFunContainer af) => af.applyFun (inputs, ruleTree)
      , (UserError ue) => RTValueOrErr (ue)
    );
  }

  nothrow @safe size_t toHash () const {
    assert (0, `TODO: Rule hash`);
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

import std.algorithm;
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
    void recurse (RuleTree * subT, BranchingParam bp) {
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
    sink ("RuleTree {\n");
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
    , ref RuleTree ruleTree
  ) {
    return RTValueOrErr (`Not implemented`);
  };

  auto rArgs = [TypeOrSymbol (`Example`), TypeOrSymbol (`rule`)];
  auto rule = Rule (rArgs, justErr);
  auto tree = RuleTree ([rule]);

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

import intrinsics;
struct RuleScope {
  @disable this ();
  Rule [] rules;
  this (Rule [] rules) {
    this.rules = rules;
  }
}
