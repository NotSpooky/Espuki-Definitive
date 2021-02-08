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
private union EArg {
  string identifierOrSymbol;
  RTValue literalValue;
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
  /// Expressions with underscores or without a previous value passed
  /// don't add the previous value as implicit first argument.
  bool usesUnderscore = false;

  nothrow @safe size_t toHash () const {
    return toHash (0);
  }
  nothrow @safe size_t toHash (size_t preHash) const {
    preHash = name.hashOf (usesUnderscore.hashOf (preHash));
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

/// Parses a list of tokens with format
/// identifier * ((Type | Symbol identifier+) * identifier) ?
MaybeParams ruleParams (Token [] tokens, ValueScope scope_) {
  Appender! (TypeOrSymbol []) rulePsToRet;
  Appender! (InputParam []) paramsToRet;
  
  with (Token.Type) {
    for (
      // Actually need the i.
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
        auto type = scope_.find (current.strVal);
        assert (type.type == Kind, `Types should be of type Kind`);
        rulePsToRet ~= TypeOrSymbol (type.value.get!TypeId);
        i ++;
        auto nextT = tokens [i];
        assert (nextT.type == identifier, `TODO: Type constructors`);
        paramsToRet ~= InputParam (nextT.strVal, i);
      }
    }
  }
  return MaybeParams (RuleParamsWithArgs (rulePsToRet [], paramsToRet []));
}

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
    if (tokens.front.type != closingBracket) {
      parseElement:
        auto subArgs = toExpressionArgs (tokens, scope_);
        if (subArgs._is!UserError) {
          throw new Exception (subArgs.get!UserError.message);
        }
        if (tokens.empty) {
          throw new Exception (errMessage ~ ` and finished line.`);
        }
        auto subExprArgs = subArgs.get! (ExpressionArg []);
        contents ~= subExprArgs;
        if (tokens.front.type == comma) {
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
) {
  //debug writeln (`Parsing: `, tokens);
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
          // TODO: Parse subexpressions instead of searching for first occurrence.
          auto functionRuleParamEnd = tokens
            .countUntil! (t => t.type == colon);
          if (functionRuleParamEnd == -1) {
            // No function rule params.
            auto subArgs = toExpressionArgs (tokens, scope_);
            if (subArgs._is!UserError) {
              return subArgs;
            }
            auto subExprArgs = subArgs.get! (ExpressionArg []);
            if (tokens.empty || tokens.front.type != closingBracket) {
              return MaybeExpressionArgs (UserError (`No matching '}' for '{'`));
            }
            // Expression [] needs to be stored as void * to avoid forward
            // reference errors.
            auto ptr = new Expression [][1];
            ptr [0] = [Expression (subExprArgs, Nullable!string (null))];
            toRet ~= ExpressionArg (
              RTValue (ArrayOfExpressions, Var (Expressions (ptr.ptr)))
            );
            // '}' popped automatically.
          } else {
            // There are function rule params.
          }
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
          auto otherTypes = toExpressionArgs (tokens, scope_);
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
          return MaybeExpressionArgs (toRet []);
      }
    }
  }
  //debug writeln (`Parsed expression args: `, toRet []);
  return MaybeExpressionArgs (toRet []);
}
