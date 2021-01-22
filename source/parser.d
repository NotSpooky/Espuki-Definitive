module parser;

import std.algorithm;
import std.range;
import lexer : ExpressionArg, Expression, Token, MaybeExpression;
import intrinsics;
import mir.algebraic;
debug import std.stdio;
import app : RTValue, Var, UserError;

/// Used to convert tokens to a list of:
/// identifiers in case of references,
/// strings in case of symbols
/// values in case of literals,
/// ExpressionArgs in case of subexpressions (pointer used to allow self-references).
MaybeExpression toExpression (Token [] tokens, bool producesUnderscore) {
  assert (!tokens.empty);
  import std.array : Appender, array;
  Appender! (ExpressionArg []) toRet;
  for (; !tokens.empty; tokens.popFront ()) {
    auto token = tokens.front;
    with (Token.Type) {
      import std.conv;
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
          auto untilBracket = tokens
            .countUntil! (t => t.type == closingBracket) ();
          if (untilBracket == -1) {
            return MaybeExpression (UserError (`No matching '}' for '{'`));
          }
          auto subExpr = toExpression (tokens [1 .. untilBracket], false);
          if (subExpr._is! UserError) {
            return subExpr;
          } else {
            assert (subExpr._is!Expression);
            Expression * toAdd = new Expression;
            *toAdd = subExpr.get!Expression;
            toRet ~= ExpressionArg (toAdd);
          }
          // Note: Closing bracket is popped at loop end.
          tokens = tokens [untilBracket .. $];
          break;
        default:
          debug writeln (`TODO: toExpression with token `, token.type);
      }
    }
  }
  //debug writeln (`Parsed expression args: `, toRet []);
  return MaybeExpression (Expression (toRet [], producesUnderscore));
}
