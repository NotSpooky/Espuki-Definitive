/+
  The basic algorithm is the following:
  Scope = Ref Value [Identifier] }
  Expression = (
    // String would be a 'name
    Identifier | string | RTValue [] parts
    , bool producesUnderscore
    , string? name
    // Using underscore OR not receiving a lastResult removes implicit first argument
    , bool usesUnderscore
  )
  // Might merge intrinsics with globals, seems to make sense.
  mut scopes = [
    Scope ([ all intrinsics ... ])
    , Scope ([ all globals ... ])
  ]
  execute Expression [] expressions:
    expressions.reduce (expression : Expression, lastResult : RTValue? {
      // Should also check that no other rule matches.
      scopes.flatten only that is no_error { matches expression lastResult }
        _ : multiple found: UserError (
          `Multiple possible rules for `, expression, `: ` _
        )
        nothing found : UserError (`No rule found that matches `, expression)
        _ : _.apply  (expression, lastResult) -> result : RTValue
        if result.name! {
          not null result.name in scopes.flatten {
            UserError (`Identifier `, result.name ,` already exists`)
          } , {
            *scopes.last.add result.name to result
            null
          }
        }

        if expression producesUnderscore:
          result
        else
          null
    })

  RuleTree tree matches Expression expression RTValue? lastResult:
    tree find (
      if (not expression usesUnderscore) and lastResult!
        // Add implicit first arg
        [ lastResult.type ] else []
    ) ~ expression.arguments.map {
      Identifier : scopes.flatten [ _ ] // Note: Can error, and might be faster to precalculate this
      string : _
      RTValue : type
    }
    

  // A rule must be matchable and appliable to an expression
  // apply Rule rule Expression expression : RTValue
   
+/

import mir.algebraic;

private uint lastTypeId;
struct Type {
  //@disable this (); // Cannot disable when assigning to Variant :(
  uint id;
  string name; // Just for pretty printing.
  this (string name) {
    this.name = name;
    this.id = lastTypeId;
    lastTypeId ++;
  }
  bool opEquals()(auto ref const Type other) const {
    return other.id == this.id;
  }
}
alias Var = Variant! (float, string, int);

/// A value in the interpreter.
struct RTValue {
  Type type;
  Var value;
  this (Type type, Var value) {
    this.type = type;
    this.value = value;
  }
  void toString (
    scope void delegate (const (char)[]) sink
  ) {
    sink (type.name);
    sink (` `);
    sink (value.toString ());
  }
}

/// An error in the code that the compiler/interpreter should show.
struct UserError {
  string message;
}

alias ValueOrErr = Nullable!RTValue;
alias ApplyFun = ValueOrErr delegate (
  RTValue [] apply
  , RuleScope [] scopes
  , bool usedUnderscore
);

debug import std.stdio;
import std.range;
auto executeFromLines (R)(R lines) if (is (ElementType!R == string)) {
  import lexer : Expression, asExpressions;
  return asExpressions (lines).visit! (
    (Expression [] expressions) { 
      foreach (expression; expressions) {
        debug expression.writeln ();
      }
      return RTValue (I32, Var (777));
    }
    , (UserError ue) {
      stderr.writeln (`Error: `, ue.message);
      return ue;
    }
  );
}

alias TypeOrSymbol = Variant! (Type, string);
struct Rule {
  @disable this ();
  TypeOrSymbol [] args;
  // Can assume that execute has correct arg types.
  ApplyFun execute;
  this (TypeOrSymbol [] args, ApplyFun execute) {
    assert (args.length > 0, `Rule with no args`);
    this.args = args;
    this.execute = execute;
  }
}

/+
  // Note: Trees must have at least one rule in them.
  // For a single scope, a RuleTree has shape:
  RuleTree = (
    (Type | Symbol) [] commonParams
    , (RuleTree | Rule) [Type | Symbol | Null ] branches
    , RuleTree? parent
  )

  // Then, a separate array, stores the pointers to the scope's rules
  ScopeRules = (
    (WeakPtr Rule) [] rules
  )
  ScopeRules [] scopesRules

  Mut RuleTree tree addRule Rule rule Index rulePos Mut LastScope scope = {
    // TODO: Modify scope
    rule args -> rArgs [rulePos .. $]
    tree commonParams -> common;
    common length -> commonPLen;
    rArgs untilDifferent common -> newPos;
    merged if (rArgs length) == newPos { null } else { rArgs [newPos] }
      -> branchStart;
    if newPos >= commonPLen {
      rulePos + newPos + branchStart? 1 : 0 -> branchRulePos
      if branchStart in tree branches {
        // Already exists.
        tree branches [branchStart] visit [
          // It's a subtree, so let's add the rule to it
          RuleTree: add rule branchRulePos scope
          // Only a rule exists, so it's a conflict.
          , Rule: UserError (text (`The rule `, rule, ` already exists in the scope`))
        ]
      } else {
        // No branch currently starts at branchStart, so let's just add a leaf.
        *tree branches [branchStart] = merged if newPos == commonPLen { 
          // No more args to parse, just add a rule
          rule
        } else {
          // Still need to check last args. A new tree is used for that.
          RuleTree rArgs [newPos + 1 .. $ - 1] [(rArgs last) : rule] tree
        }
      }
    } else {
      assert newPos < commonPLen
      // As the rule is smaller, we just branch before the current branching
      // point (at newPos).

      // Give the rest of common parameters to the new tree's common
      // The branches of the new tree will be the ones this tree had.
      RuleTree common [newPos + 1 .. $] (tree branches) tree -> newTree;

      *tree branches = [null : rule, common [newPos] : newTree]
      // Last common params were sent to the new tree, so we remove them from
      // here.
      *tree commonParams = tree commonParams [0 .. newPos]
    }
  }
+/

alias ScopeRule = RuleTree; // Weak reference
  
// Pointer because of structure self-reference.
alias Branch = Variant! (RuleTree *, Rule);

alias BranchingParam = Variant! (Type, string, typeof (null));

private alias ParentTreeRef = Nullable! (RuleTree *);

import std.algorithm;
/// An easily searchable tree structure to match Expressions with Rules.
struct RuleTree {
  TypeOrSymbol [] commonParams;
  /// Key is the first param in the rule that isn't in the others.
  /// Null if no different parameters (eg. a rule might start the same as others
  /// but the other ones have extra parameters).
  Branch [BranchingParam] branches;

  ParentTreeRef parent;
  /// Adds a new rule to the tree.
  /// Returns the corresponding ScopeRule of the newly added rule
  void addRule (Rule rule, ref RuleScope scope_, size_t ruleArgStartIndex = 0) {
    auto rArgs = rule.args [ruleArgStartIndex .. $];
    const commonPLen = commonParams.length;
    // zip -> countUntil didn't seem to work, so manual loop is used
    debug import std.conv : to, text;
    size_t branchingPos = rArgs.length;
    auto branchStart = BranchingParam (null);
    foreach (i, rArg; rArgs) {
      if (commonParams.length == i || rArg != commonParams [i]) {
        branchingPos = i;
        branchStart = BranchingParam (rArgs [i + 1]);
        break;
      }
    }

    debug writeln (`Branching pos is `, branchingPos, ` and branchStart `, branchStart);
    if (branchingPos == commonParams.length) {
      // The rule has all the commonParams and maybe more.
      debug writeln (`Rule has >= params than the tree`);
      auto inBPos = branchStart in branches;
      if (inBPos) {
        debug writeln (`Branched on the same path before: `, inBPos);
        if ((* inBPos)._is! (RuleTree *)) {
          // Just add to the subtree
          const subTreeRuleStart = ruleArgStartIndex + branchingPos + 1;
          auto subTree = (* inBPos).get! (RuleTree *);
          subTree.addRule (rule, scope_, subTreeRuleStart);
        } else {
          // There's a rule stored here.
          assert ((* inBPos)._is!Rule);
          auto currentRule = (* inBPos).get!Rule;
          // Might need to either create a subtree with common [] and null key
          // to that rule + first of rArgs to another subtree with the
          // new rule or error if there's no more rArgs, as there would be
          // ambiguous rules.
          if (branchingPos == rArgs.length) {
              // TODO: Change to UserError
              throw new Exception (text (
                `Rule `, rule
                , ` has same parameters as existing one: `, currentRule
              ));
          }
          auto newSubSubTree = new RuleTree (
            rArgs [branchingPos + 2 .. $]
            , [ BranchingParam (null) : Branch (rule)]
          );

          auto newSubTree = new RuleTree (
            []
            , [
              BranchingParam (null) : (* inBPos)
              , BranchingParam (rArgs [branchingPos + 1]) : Branch (newSubSubTree)
            ]
            , ParentTreeRef (& this)
          );
          newSubSubTree.parent = ParentTreeRef (newSubTree);
          this.branches [branchStart] = Branch (newSubTree);
        }
      } else {
        // The branch start is not on this.branches, so let's just add it.
        if (branchingPos == rArgs.length) {
          branches [branchStart] = Branch (rule);
        } else {
          branches [branchStart] = Branch (new RuleTree (
            rArgs [branchingPos + 1 .. $]
            , [BranchingParam (null) : Branch (rule)]
          ));
        }
      }
    } else {
      debug writeln (`Rule has < params than the tree`);
      assert (branchingPos < commonParams.length);
      // As the rule is smaller, we just branch before the current branching
      // point (at newPos).

      // Give the rest of common parameters to the new tree's common
      // The branches of the new tree will be the ones this tree had.
      auto newSubTree = new RuleTree (
        this.commonParams [branchingPos + 1 .. $]
        , this.branches
        , ParentTreeRef (&this)
      );
      this.branches = [
        BranchingParam (null) : Branch (rule)
        , BranchingParam (branchStart) : Branch (newSubTree)
      ];
      // Last common params were sent to the new tree, so we remove them from
      // here.
      this.commonParams = this.commonParams [0 .. branchingPos];
    }
  }
}

unittest {
  auto ruleScope = RuleScope ([]);
  auto rArgs = [TypeOrSymbol (`Example`), TypeOrSymbol (`rule`)];
  auto justErr = delegate (
    RTValue [] apply
    , RuleScope [] scopes
    , bool usedUnderscore
  ) {
    return ValueOrErr ();
  };
  auto rule = Rule (rArgs, justErr);
  auto tree = RuleTree (
    [rArgs [0]],
    [BranchingParam (rArgs [1]) : Branch (rule)]
  );
  
  auto smallerRArgs = [rArgs [0]];
  auto smallerRule = Rule (smallerRArgs, justErr);
  tree.addRule (smallerRule, ruleScope);
  assert (tree.commonParams == smallerRArgs);
  assert (BranchingParam (rArgs [1]) in tree.branches);
  assert (BranchingParam (null) in tree.branches);
}

import intrinsics;
struct RuleScope {
  @disable this ();
  Rule [] rules;
  this (Rule [] rules) {
    this.rules = rules;
  }

  /+
  // Didn't let me use a Nullable!Value instead of pointer :(
  ValueOrErr execute (
    AsValueListRet valListWithUnderscore
    , RuleScope [] scopes
    , IdentifierScope lastIdScope
    , bool inferUnderscore
    , Value * underscoreVal
  ) {
    auto args = valListWithUnderscore.values;
    writeln (`Executing `, valListWithUnderscore, `. Infer _? `, inferUnderscore);
    auto validMatches = rules.filter! ((rule) {
      if (inferUnderscore) {
        // First non-string arg is automatically inserted from _
        if (rule.args.length != args.length + 1) return false;
        bool alreadyPlacedImplicitUnderscore = false;
        auto argsCopy = args.save;
        foreach (i, ruleArg; rule.args) {
          if (ruleArg.type == typeid (string)) {
            auto arg = argsCopy.front;
            // In case of strings, make sure the value has the same string
            if (!(arg.type == Identifier && arg.value.get!string == ruleArg.get!string)) {
              // Text differs
              return false;
            }
          } else if (alreadyPlacedImplicitUnderscore) {
            auto arg = argsCopy.front;
            // A value argument.
            assert (ruleArg.type == typeid (Type));
            if (arg.type != ruleArg.get!Type) {
              return false;
            }
          } else {
            alreadyPlacedImplicitUnderscore = true;
            // A value argument. We will insert the value that the underscore points to.
            assert (underscoreVal != null);
            if (underscoreVal.type != ruleArg.get!Type) {
              return false;
            } else {
              args = args [0..i] ~ *underscoreVal ~ args [i..$];
              // Don't pop args as we didn't use an arg.
              continue;
            }
          }
          argsCopy.popFront ();
        }
        return true;
      } else { // Don't infer underscore.
        // Args should appear in the same order as the rule.
        if (rule.args.length != args.length) return false;
        return args.zip (rule.args).all! ((pair) {
          auto arg = pair [0];
          auto ruleArg = pair [1];
          if (ruleArg.type == typeid (string)) {
            // In case of strings, make sure the value has the same string/
            return arg.type == Identifier && arg.value.get!string == ruleArg.get!string;
          } else {
            assert (ruleArg.type == typeid (Type));
            return arg.type == ruleArg.get!Type;
          }
        });
      }
    }).array;
    if (validMatches.length == 0) {
      stderr.writeln (`No valid rule in scope level for `, args);
      return ValueOrErr ();
    } else if (validMatches.length > 1) {
      stderr.writeln (
        `Multiple matching rules for `
        , args
        , validMatches.map!`"\n\t" ~ a.to!string`.joiner ()
      );
      return ValueOrErr ();
    }
    writeln (`Got as args to execute: `, args);
    return validMatches [0].execute (
      args
      , scopes
      , lastIdScope
      , valListWithUnderscore.usedUnderscore
    );
  }
  +/
}
