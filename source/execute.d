/+
  The basic algorithm is the following:
  Scope = { valueRef [Identifier] }
  InterpreterValue = { RTValue value }
  Expression = {
    // String would be a 'name
    Identifier | string | RTValue [] parts
    , bool producesUnderscore
    , string? name
    // Using underscore OR not receiving a lastResult removes implicit first argument
    , bool usesUnderscore
  }
  // Might merge intrinsics with globals, seems to make sense.
  mut scopes = [
    Scope ([ all intrinsics ... ])
    , Scope ([ all globals ... ])
  ]
  execute Expression [] expressions:
    expressions.reduce (expression : Expression, lastResult : InterpreterValue? {
      // Should also check that no other rule matches.
      scopes.flatten only that is no_error { matches expression lastResult }
        _ : multiple found: UserError (
          `Multiple possible rules for `, expression, `: ` _
        )
        nothing found : UserError (`No rule found that matches `, expression)
        _ : _.apply  (expression, lastResult) -> result : InterpreterValue
        // TODO: Check for name conflicts
        if result.name! { *scopes.last.add name to result }

        if expression producesUnderscore:
          result
        else
          null
    })

  RuleTree tree matches Expression expression InterpreterValue? lastResult:
    tree find (
      if (not expression usesUnderscore) and lastResult!
        // Add implicit first arg
        [ lastResult.type ] else []
    ) ~ expression.arguments.map {
      Identifier : scopes.flatten [ _ ] // Note: Can error
      string : _
      RTValue : type
    }
    

  // A rule must be matchable and appliable to an expression
  // apply Rule rule Expression expression : InterpreterValue
   
+/
