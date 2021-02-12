import mir.algebraic;
import std.algorithm;
import std.conv : text, to;
import std.exception : enforce;
import std.typecons : Tuple, tuple;
import parser : Expression, ExpressionArg, SumTypeArgs, ArrayArgs, TupleArgs;
import rulematcher;

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
    return args [0].value.get!TypeId.toString () ~ ` []`;
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
string toString (TypeId type) {
  return globalTypeInfo [type].toString ();
}

/// As of now just handles type equality by id.
bool isSubTypeOf (TypeId type, TypeId parent) {
  if (type == parent) {
    return true;
  }
  return !type.visitTypeConvs.find (parent).empty;
}

RTValue tryImplicitConversion (in RTValue val, TypeId objective) {
  if (val.type.isSubTypeOf (objective)) {
    return val;
  } else {
    throw new Exception (
      text (val, ` canot be converted to `, globalTypeInfo [objective])
    );
  }
}

alias ApplyFun = RTValue delegate (
  in RTValue [] inputs
  , ref RuleMatcher ruleMatcher
  , ref ValueScope valueScope
);
/// mir.algebraic.Variant seems to have trouble with ApplyFun so we wrap it.
/+struct ApplyFunContainer {
  ApplyFun applyFun;
}+/

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
  , Rule *     // For RuleT
  , RTValue [] // For TupleT.
  , This []    // For arrays and structs.
  , typeof (null)
  , Expressions /* Expression [] * */
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
  Nullable!(ValueScope *) parent;
  private RTValue [string] values;
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

  Nullable!RTValue find (string name) {
    auto pNullable = nullable (&this);
    while (!pNullable.isNull) {
      auto p = pNullable.get ();
      auto nInVals = name in p.values;
      if (nInVals) {
        return nullable (*nInVals);
      }
      pNullable = p.parent;
    }
    return Nullable!RTValue (null);
  }

  auto withScope (alias F)(RTValue [string] subScopeVals) {
    foreach (name; subScopeVals.keys) {
      auto pNullable = nullable (&this);
      while (!pNullable.isNull) {
        auto p = pNullable.get ();
        enforce (
          !(name in p.values)
          , `Adding already existing name '` ~ name ~ `' to scope`
        );
        pNullable = p.parent;
      }
    }
    return F (ValueScope (nullable (&this), subScopeVals));
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

alias RTValueNullOrErr = Variant! (RTValue, typeof (null), UserError);

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
RTValue lastMatchResult (
  ref RuleMatcher ruleMatcher
  , in RTValueOrSymbol [] args
  , ref ValueScope valueScope
) {
  auto asRTVals = args.map! (arg => arg.visit! (
    (RTValue val) => val
    , (string symbol) => RTValue (Symbol, Var (symbol))
  )).array;
  if (asRTVals.length == 1) {
    return asRTVals [0];
  }
  RTValue [] lastResult;
  while (!asRTVals.empty) {
    lastResult = [ruleMatcher.matchAndExecuteRule (asRTVals, valueScope)];
    // debug writeln (`Last result is `, lastResult [0]);
  }
  assert (lastResult.length > 0);
  return lastResult [0];
}

RTValue subValue (
  const ExpressionArg [] args
  , ref RuleMatcher ruleMatcher
  , ref ValueScope scope_
) {
  return executeFromExpression (
    Expression (args, Nullable!string (null))
    , [] // Last result isn't sent to subexpressions.
      , ruleMatcher
      , scope_
    );
  }

  auto subValues (
    const ExpressionArg [][] args
    , ref RuleMatcher ruleMatcher
  , ref ValueScope scope_
) {
    return args.map! (eA => subValue (eA, ruleMatcher, scope_));
  }

  RTValue createArray (
    const ExpressionArg [][] args
    , ref RuleMatcher ruleMatcher
    , ref ValueScope scope_
  ) {
  if (args.empty) {
    return RTValue (EmptyArray, Var (null));
  }
  auto subVs = subValues (args, ruleMatcher, scope_);
  const elType = subVs.front.type;
  auto retType = arrayOf (elType);
  Var [] afterConversionArray = subVs
    .map! (s => s.tryImplicitConversion (elType).value)
    .array;
  return RTValue (retType, Var (afterConversionArray));
}

RTValue createSumType (
  const ExpressionArg [][] args
  , ref RuleMatcher ruleMatcher
  , ref ValueScope scope_
) {
  // First arg is the added type, second either a normal type or a sumtype.
  // debug writeln (`Args for sumtype: `, args);
  auto subVs = subValues (args, ruleMatcher, scope_).array;
  // debug writeln (`Types in sumtype `, subVs.map!(s => s.value.get!TypeId));
  assert (!subVs.empty);
  auto toRet = sumTypeOf (subVs);
  // Add constructors for each subtype.
  foreach (const subV; subVs) {
      (const RTValue subV) {
      ruleMatcher.addRule (new Rule (
        [RuleParam (RTValue (Kind, Var (toRet))), RuleParam (subV.value.get!TypeId)]
        , (
          in RTValue [] rArgs
          , ref RuleMatcher ruleMatcher
          , ref ValueScope valueScope
        ) {
          assert (rArgs.length == 2);
          return RTValue (toRet, rArgs [1].value);
        }
      )); 
    } (subV);
  }
  return typeToRTValue (toRet);
}

RTValue createTuple (
  const ExpressionArg [][] args
  , ref RuleMatcher ruleMatcher
  , ref ValueScope scope_
) {
  return RTValue (TupleT, Var (subValues (args, ruleMatcher, scope_).array));
  assert (0, `TODO: createTuple`);
}

/// Finds appropriate rules to match the expression and returns the result
/// of applying those rules to the match.
/// If the best match doesn't comprise the full expression, it's result is given
/// as the first argument for another match.
/// This process is repeated until the expression is exhausted or an error occurs.
RTValue executeFromExpression (
  in Expression expression
  , in RTValue [] lastResult
  , ref RuleMatcher ruleMatcher
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
          *subExpr, lastResult, ruleMatcher, scope_
        );
        return RTValueOrSymbol (subExprRet);
      }
      // Already a value, nothing to do.
      , (RTValue val) => RTValueOrSymbol (val)
      , (string a) {
        // If the string is an identifier in the scope, use that value,
        // else treat is as a symbol.
        auto inScope = scope_.find (a);
        if (inScope.isNull) {
          return RTValueOrSymbol (a);
        } else {
          return RTValueOrSymbol (inScope.get ());
        }
      }
      , (const ArrayArgs!ExpressionArg arrayElementExpressions)
        => RTValueOrSymbol (createArray (
          arrayElementExpressions.args
          , ruleMatcher
          , scope_
        ))
      , (const ExpressionArg [] subExpression)
        => RTValueOrSymbol (subValue (subExpression, ruleMatcher, scope_))
      , (const SumTypeArgs!ExpressionArg sumTypeArgs) 
        => RTValueOrSymbol (createSumType (sumTypeArgs.args, ruleMatcher, scope_))
      , (const TupleArgs!ExpressionArg tupleArgs)
        => RTValueOrSymbol (createTuple (tupleArgs.args, ruleMatcher, scope_))
    )
  ).array;
  if (args.length == 1 && args [0]._is!RTValue) {
    return args [0].get!RTValue;
  }
  debug (2) writeln (`Got as last result `, lastResult.map! (a => a.to!string));
  debug (2) writeln (`Got as args `, args.map! (a => a.visit! (b => b.to!string)));

  return lastMatchResult (ruleMatcher, args, scope_);
}

/// Chains multiple expressions together and returns the last one's return value
/// Can return UserError on error.
Nullable!RTValue executeFromExpressions (
  in Expression [] expressions
  , RTValue [] lastResult
  , ref RuleMatcher ruleMatcher
  , ref ValueScope scope_
) {
  foreach (expression; expressions) {
    auto result = executeFromExpression (
      expression, lastResult, ruleMatcher, scope_
    );
    if (expression.passThisResult) {
      // debug writeln (`res: `, result.get!RTValue.value.visit! (a => a.to!string));
      lastResult = [result];
    } else {
      lastResult = [];
    }
  }
  if (lastResult.length > 0) {
    return (Nullable!RTValue (lastResult [0]));
  } else {
    return Nullable!RTValue (null);
  }
}

debug import std.stdio;
import std.range;
RTValueNullOrErr executeFromLines (R)(R lines) if (is (ElementType!R == string)) {
  import lexer : asExpressions;
  import intrinsics : globalScope, globalRules;
  auto ruleMatcher = RuleMatcher (globalRules.rules);
  return asExpressions (lines, globalScope).visit! (
    (Expression [] expressions) { 
      return executeFromExpressions (expressions, [], ruleMatcher, globalScope)
        .visit! (res => RTValueNullOrErr (res));
    }
    , (UserError ue) {
      stderr.writeln (`Error: `, ue.message);
      return RTValueNullOrErr (ue);
    }
  );
}

size_t amountThatAreType (R)(R args) {
  return args.filter ! (arg => arg._is!Type).count ();
}

struct Rule {
  @disable this ();
  import rulematcher : RuleParam;
  RuleParam [] params;
  ApplyFun applyFun;
  this (
    RuleParam [] params
    , ApplyFun applyFun
  ) {
    assert (params.length > 0, `Rule with no params`);
    this.params = params;
    this.applyFun = applyFun;
  }

  nothrow @safe size_t toHash () const {
    assert (0, `TODO: Rule hash`);
  }
}

import intrinsics;
struct RuleScope {
  @disable this ();
  Rule [] rules;
  this (Rule [] rules) {
    this.rules = rules;
  }
}
