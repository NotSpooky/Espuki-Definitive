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

struct SumTypeArgs (T) {
  T [][] args;
}
struct ArrayArgs (T) {
  T [][] args;
}
struct TupleArgs (T) {
  T [][] args;
}
struct UnderscoreIdentifier {
  uint argPos;
}
private union EArg {
  string identifierOrSymbol;
  RTValue literalValue;
  UnderscoreIdentifier underscoreId;
  This [] subExpression;
  ArrayArgs!This arrayArgs;
  SumTypeArgs!This sumTypeArgs;
  TupleArgs!This tupleArgs;
}

alias ExpressionArg = TaggedVariant!EArg;

/// Don't construct this directly, use 'parser.toExpression' function.
struct Expression {

  const ExpressionArg [] args;
  /// An expression gets a name when assigned to a variable.
  /// Note that the implicit underscore isn't handled with this variable.
  Nullable!string name;
  /// Results are saved to first arg if this is true.
  bool passThisResult = true;

  nothrow @safe size_t toHash () const {
    return toHash (0);
  }
  nothrow @safe size_t toHash (size_t preHash) const {
    preHash = name.hashOf (preHash);
    foreach (arg; args) {
      arg.visit! (
        (Expression * subExpression) { preHash = (* subExpression).toHash (preHash); }
        , (a) { a.hashOf (preHash); }
      );
    }
    return preHash;
  }
}

import execute : TypeOrSymbol, ValueScope, InputParam;
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

ExpressionArg [][] nested (
  ref Token [] tokens
  , in ValueScope scope_
  , Token.Type rightDelimiter
  , Token.Type separator = Token.Type.comma
) {
  const errMessage = `Didn't find matching '` ~ rightDelimiter.to!string ~ `'`;
  if (tokens.empty) {
    throw new Exception (errMessage);
  }
  // First is left delimiter.
  tokens.popFront ();
  ExpressionArg [][] contents;
  with (Token.Type) {
    if (tokens.front.type != rightDelimiter) {
      parseElement:
        auto subArgs = toExpressionArgs (tokens, scope_, [separator, rightDelimiter]);
        if (subArgs._is!UserError) {
          throw new Exception (subArgs.get!UserError.message);
        }
        if (tokens.empty) {
          throw new Exception (errMessage ~ ` and finished line.`);
        }
        auto subExprArgs = subArgs.get! (ExpressionArg []);
        contents ~= subExprArgs;
        if (tokens.front.type == separator) {
          tokens.popFront ();
          goto parseElement;
        }
      if (tokens.front.type != rightDelimiter) {
        throw new Exception (errMessage);
      }
      // rightDelimiter is popped automatically by the popFront
      // in toExpressionArgs loop.
    }
    return contents;
  }
}

struct Success {}
alias SuccessOrError = Variant! (Success, UserError);
alias MaybeExpressionArgs = Variant! (ExpressionArg [], UserError);
/// Used to convert tokens to a list of:
/// strings in case of symbols or identifiers
/// values in case of literals,
/// ExpressionArgs in case of subexpressions (pointer used to allow self-references).
/// Note: Receives tokens by ref and advances it until the expression is parsed.
MaybeExpressionArgs toExpressionArgs (
  ref Token [] tokens
  , in ValueScope scope_
  , Token.Type [] delimiters = []
) {
  //debug writeln (`Parsing: `, tokens);
  assert (!tokens.empty);
  Appender! (ExpressionArg []) toRet;
  for (; !tokens.empty; tokens.popFront ()) {
    auto token = tokens.front;
    // debug writeln (`T: `, token);
    with (Token.Type) {
      foreach (delimiter; delimiters) {
        if (token.type == delimiter) {
          goto lexEnd;
        }
      }
      switch (token.type) {
        case identifier:
          toRet ~= ExpressionArg (token.strVal);
          break;
        case underscoreIdentifier:
          debug stderr.writeln (`TODO: Manage underscore identifiers`);
          string num = token.strVal [1..$];
          uint argPos = 0;
          if (!num.empty) {
            argPos = num.to!uint;
          } 
          toRet ~= ExpressionArg (UnderscoreIdentifier (argPos));
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
          /+auto functionRuleParamEnd = tokens
            .countUntil! (t => t.type == colon);+/
          auto subExprs = nested (
            tokens, scope_, closingBracket, colon
          );
          assert (subExprs.length == 1, `TODO: Manage functions with rule params`);
          auto ptr = new Expression [][1];
          ptr [0] = [Expression (subExprs [0], Nullable!string (null))];
          toRet ~= ExpressionArg (
            RTValue (ArrayOfExpressions, Var (Expressions (ptr.ptr)))
          );
          break;
        case openingParenthesis:
          auto subExprs = nested (
            tokens, scope_, closingParenthesis, comma
          );
          if (subExprs.length == 1) {
            toRet ~= ExpressionArg (subExprs [0]);
          } else {
            toRet ~= ExpressionArg (TupleArgs!ExpressionArg (subExprs));
          }
          break;
        case openingSquareBracket:
          // Array syntax.
          toRet ~= ExpressionArg (ArrayArgs!ExpressionArg (nested (
            tokens, scope_, closingSquareBracket, comma
          )));
          break;
        case verticalLine:
          tokens.popFront ();
          if (tokens.empty) {
            return MaybeExpressionArgs (UserError (
              `Cannot end line with '|'`
            ));
          }
          auto otherTypes = toExpressionArgs (tokens, scope_, delimiters);
          if (otherTypes._is!UserError) {
            return otherTypes;
          }
          auto otherTypesAsEA = otherTypes.get! (ExpressionArg []);
          assert (otherTypesAsEA.length == 1);
          auto accum = otherTypesAsEA [0];
          auto toRetArr = [toRet []];
          SumTypeArgs!ExpressionArg genSumType;
          if (accum._is! (SumTypeArgs!ExpressionArg)) {
            // Flatten the SumTypeArgs to a single one.
            genSumType = SumTypeArgs!ExpressionArg (
              toRetArr ~ accum.get!(SumTypeArgs!ExpressionArg).args
            );
          } else {
            // expression to type | the next expression to type
            genSumType = SumTypeArgs!ExpressionArg (
              toRetArr ~ otherTypesAsEA
            );
          }
          auto eA = ExpressionArg (genSumType);
          return MaybeExpressionArgs ([eA]);
        default:
          assert (0, `Unexpected token ` ~ token.to!string);
      }
    }
  }
  lexEnd:
  return MaybeExpressionArgs (toRet []);
}
