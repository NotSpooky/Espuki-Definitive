module parser;

import std.algorithm;
import std.conv;
import std.range;
import lexer : Token;
import intrinsics;
import mir.algebraic;
import std.array : Appender, array;
debug import std.stdio;
import execute;

/// Don't construct this directly, use 'parser.toExpression' function.
struct Expression {

  ExpressionArg [] args;
  /// An expression with return value that isn't finished with the semicolon token.
  /// is true, false otherwise.
  bool producesUnderscore;
  /// An expression gets a name when assigned to a variable.
  /// Note that the implicit underscore isn't handled with this variable.
  Nullable!string name;
  /// Expressions with underscores or without a previous value passed
  /// don't add the previous value as implicit first argument.
  bool usesUnderscore = false;


  nothrow @safe size_t toHash () const {
    return toHash (0);
  }
  nothrow @safe size_t toHash (size_t preHash) const {
    preHash = producesUnderscore.hashOf (name.hashOf (producesUnderscore.hashOf ()));
    foreach (arg; args) {
      arg.visit! (
        (Expression * subExpression) { preHash = (* subExpression).toHash (preHash); }
        , (a) { a.hashOf (preHash); }
      );
    }
    return preHash;
  }
}

private union EArg {
  string identifierOrSymbol;
  RTValue literalValue;
  Expression * subExpression;
}

alias ExpressionArg = TaggedVariant!EArg;

import execute : TypeOrSymbol, TypeScope, InputParam;
struct RuleParamsWithArgs {
  TypeOrSymbol [] ruleParams;
  InputParam [] inputParams;
}
alias MaybeParams = Variant! (RuleParamsWithArgs, UserError);

// Function syntax:
/+
{ I32 arg1, String arg2 -> RetType :
  arg1 ...
}

function is stored on an RTValue, same as literals
+/

/// Parses a list of tokens with format
/// identifier * ((Type | Symbol identifier+) * identifier) ?
MaybeParams ruleParams (Token [] tokens, TypeScope typeScope) {
  Appender! (TypeOrSymbol []) rulePsToRet;
  Appender! (InputParam []) paramsToRet;
  
  with (Token.Type) {
    for (
      uint i = 0
      ; i < tokens.length
      ; i ++
    ) {
      auto current = tokens [i];
      if (current.type == identifier) {
        rulePsToRet ~= TypeOrSymbol (current.strVal);
      }
      if (current.type == typeIdentifier) {
        if (tokens.length < 2) {
          return MaybeParams (UserError (
            text (`Expected identifiers after `, current.strVal)
          ));
        }
        auto type = current.strVal in typeScope.types;
        if (!type) {
          return MaybeParams (UserError (
            text (`Couldn't find type `, current.strVal)
          ));
        }
        rulePsToRet ~= TypeOrSymbol (*type);
        i ++;
        auto nextT = tokens [i];
        assert (nextT.type == identifier, `TODO: Type constructors`);
        paramsToRet ~= InputParam (nextT.strVal, i);
      }
    }
  }
  return MaybeParams (RuleParamsWithArgs (rulePsToRet [], paramsToRet []));
}

struct Success {}
alias SuccessOrError = Variant! (Success, UserError);
alias MaybeExpression = Variant! (Expression, UserError);
/// Used to convert tokens to a list of:
/// strings in case of symbols or identifiers
/// values in case of literals,
/// ExpressionArgs in case of subexpressions (pointer used to allow self-references).
MaybeExpression toExpression (
  Token [] tokens
  , bool producesUnderscore
  , TypeScope typeScope
) {
  assert (!tokens.empty);
  Appender! (ExpressionArg []) toRet;
  for (; !tokens.empty; tokens.popFront ()) {
    auto token = tokens.front;
    with (Token.Type) {
      switch (token.type) {
        case identifier:
          toRet ~= ExpressionArg (token.strVal);
          break;
        case floatLiteral:
          debug (2) stderr.writeln (`TODO: Store float literals in infinite-precision`);
          toRet ~= ExpressionArg (RTValue (F32, Var (token.strVal.to!float)));
          break;
        case integerLiteral:
          debug (2) stderr.writeln (`TODO: Store integer literals in infinite-precision`);
          toRet ~= ExpressionArg (RTValue (I32, Var (token.strVal.to!int)));
          break;
        case stringLiteral:
          toRet ~= ExpressionArg (RTValue (String, Var (token.strVal)));
          break;
        case openingBracket:
          // Note: This will also be used for storing graphs, in case there's no
          // colon.
          tokens.popFront ();
          auto functionRuleParamEnd = tokens
            .countUntil! (t => t.type == colon);

          SuccessOrError untilBracketToExpressions () {
            auto untilBracket = tokens
              .countUntil! (t => t.type == closingBracket);
            if (untilBracket == -1) {
              return SuccessOrError (UserError (`No matching '}' for '{'`));
            }
            auto funExpr = toExpression (
              tokens [0 .. untilBracket]
              , false // TODO: Check
              , typeScope
            );
            if (funExpr._is!UserError) {
              return SuccessOrError (funExpr.get!UserError);
            }
            debug writeln (
              `TODO: Allow multiple expressions in functions`
            );
            auto expressionPtr = new Expression [][1];
            expressionPtr [0] = [funExpr.get!Expression];
            toRet ~= ExpressionArg (RTValue (Function, Var (
              expressionPtr.ptr
            )));
            // Note: Closing bracket is popped at loop end.
            tokens = tokens [untilBracket .. $];
            return SuccessOrError (Success ());
          }
          if (functionRuleParamEnd == -1) {
            // No function rule params.
            auto tried = untilBracketToExpressions ();
            if (tried._is!UserError) {
              return MaybeExpression (tried.get!UserError);
            }
          } else {
            // There are function rule params.
            auto maybeRuleP
              = ruleParams (tokens [0.. functionRuleParamEnd], typeScope);
            if (maybeRuleP._is!UserError) {
              return MaybeExpression (maybeRuleP.get!UserError);
            }
            auto ruleP = maybeRuleP.get!RuleParamsWithArgs;
            // Colon here, so pop it.
            tokens.popFront ();
            auto tried = untilBracketToExpressions ();
            if (tried._is!UserError) {
              return MaybeExpression (tried.get!UserError);
            }
          }
          break;
        default:
          debug writeln (`TODO: toExpression with token `, token.type);
      }
    }
  }
  //debug writeln (`Parsed expression args: `, toRet []);
  return MaybeExpression (Expression (toRet [], producesUnderscore));
}
