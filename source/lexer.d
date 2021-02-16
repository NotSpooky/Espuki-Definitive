module lexer;

import std.conv;
import std.range;
import mir.algebraic;
import std.algorithm;
import execute : RTValue, UserError, ValueScope;
import std.array;
import std.exception;

struct Token {
  string strVal;
  enum Type {
    comma
    , dot
    , openingBracket
    , closingBracket
    , openingParenthesis
    , closingParenthesis
    , openingSquareBracket
    , closingSquareBracket
    , floatLiteral
    , integerLiteral
    , stringLiteral
    , identifier            // For variable names and symbols
    , underscoreIdentifier  // _[0-9]+ has special meaning in this language
    , colon
    , semicolon             // Outside of this module, this shouldn't appear
    , rightArrow
    , verticalLine          // Used for sumtypes
  }
  Type type;
}

debug import std.stdio;

import parser : Expression, ExpressionArg, toExpressionArgs;
alias LexRet = Variant! (Expression [], UserError);

// Mutable mess :)
// Absolutely not proud of this function.
/// Tries to generate a list of expressions from text.
/// Note: Doesn't return a list of tokens.
/// Those are handled here direclty or by using parser.toExpressionArgs
LexRet asExpressions (R)(R inputLines, in ValueScope scope_) {
  Appender! (Expression []) toRet;
  // Outside the loop as output lines might not have a 1:1 relationship with
  // input lines in cases such as empty/commented lines or '\' at the end of
  // a line.
  alias TokenAppender = Appender! (Token []);
  TokenAppender currentLineTokens;

  import std.string;
  // TODO: Don't read the entire file at once.
  auto input = inputLines.joiner ("\n").to!string;
  // Note: Jumping to this label doesn't execute a popFront at the start.
  lexLine:
  while (!input.empty) {
    input = input.stripLeft ();
    Nullable! (Token.Type) type;
    with (Token.Type) {
      switch (input.front) {
        case ',':
          type = comma;
          break;
        case '.':
          type = dot;
          break;
        case '{':
          type = openingBracket;
          break;
        case '}':
          type = closingBracket;
          break;
        case '(':
          type = openingParenthesis;
          break;
        case ')':
          type = closingParenthesis;
          break;
        case '[':
          type = openingSquareBracket;
          break;
        case ']':
          type = closingSquareBracket;
          break;
        case ':':
          type = colon;
          break;
        case '|':
          type = verticalLine;
          break;
        case ';':
          auto currentLineData = currentLineTokens [];
          if (currentLineData.length == 0) {
            return LexRet (UserError (`; found with empty left side`));
          } else {
            input.popFront ();
            auto exprArgs = toExpressionArgs (
              currentLineData
              , scope_
            );
            if (exprArgs._is! (ExpressionArg [])) {
              toRet ~= Expression (
                exprArgs.get! (ExpressionArg [])
                , Nullable!string (null)
                , false
              );
            } else {
              assert (exprArgs._is!UserError);
              return LexRet (exprArgs.get!UserError);
            }
            currentLineTokens = TokenAppender ();
            continue;
          }
        default:
          break;
      }
      if (!type.isNull ()) {
        // Was a single-character token.
        currentLineTokens ~= Token (input.front.to!string, type.get ());
        input.popFront ();
        continue;
      }
      // Not in the single-character token list.
      // Note that some regexes in this else are single character ones.
      if (input.startsWith (`->`)) {
        input = input [2 .. $];
        assert (0, `TODO: Variable assignment token`);
        // currentLineTokens ~= Token (input [], Token.Type.rightArrow);
        // continue;
      } else if (input.startsWith (`//`)) {
        if (!input.findSkip ("\n")) {
          // Comment ends at EOF.
          break;
        }
        continue;
      } else if (input.startsWith (`/*`)) {
        input = input [2 .. $];
        enforce (input.findSkip (`*/`), `No matching '*/' for '/*'`);
        continue;
      } else if (input.startsWith (`/+`)) {
        input = input [2 .. $];
        // Nestable comment
        int plusCommentDepth = 1;
        while (plusCommentDepth > 0) {
          if (input.empty) {
            throw new Exception (`No matching '+/' for '/+'`);
          } else if (input.startsWith (`+/`)) {
            plusCommentDepth --;
            input = input [2 .. $];
          } else if (input.startsWith (`/+`)) {
            plusCommentDepth ++;
            input = input [2 .. $];
          } else {
            // Didn't match boundary: still inside comment.
            input.popFront;
          }
        }
        continue;
      } // End of comment handling.
      // Multi-character token.
      import std.regex;
      struct RegexType {
        alias CTReg = typeof (ctRegex!``);
        CTReg regexS;
        Token.Type type;
      }
      if (input.front == '"') {
        // String literal.
        input.popFront ();
        Appender!string toAdd = "";
        while (true) {
          enforce (!input.empty, `Unfinished string literal`);
          if (input.front == '\\') {
            // Escape characters.
            input.popFront ();
            switch (input.front) {
              case '\\': case '"':
                toAdd ~= input.front ();
                break;
              case 'n':
                toAdd ~= '\n';
                break;
              case 'r':
                toAdd ~= '\r';
                break;
              case 't':
                toAdd ~= '\t';
                break;
              default:
                assert (0, `TODO: Handle string literal escaping`);
            }
            input.popFront ();
          } else if (input.front == '"') {
            // Finished string literal.
            currentLineTokens ~= Token (toAdd [], stringLiteral);
            input.popFront ();
            goto lexLine; // Continue on outside loop.
          } else {
            // Single non-escaped character.
            toAdd ~= input.front ();
            input.popFront ();
          }
        }
      } // End of string literal handling.
      enum regexTypes = [
        RegexType (ctRegex!`^(?:\-?[0-9]+)\.[0-9]+`, floatLiteral)
        , RegexType (ctRegex!`^\-?[0-9]+`, integerLiteral)
        /+, RegexType (ctRegex!`^\p{Ll}[\w]*`, identifier)
        , RegexType (ctRegex!`^\p{Lu}[\w]+`, typeIdentifier) +/
        , RegexType (ctRegex!`^\_[0-9]*`, underscoreIdentifier)
        , RegexType (ctRegex!`^\+|\-|\*|\/|(?:\w+)`, identifier)
      ];
      bool foundMatchingRegex = false;
      foreach (regType; regexTypes) {
        auto matched = input.matchFirst (regType.regexS);
        if (!matched.empty) {
          foundMatchingRegex = true;
          auto matchedStr = matched.front;
          currentLineTokens ~= Token (matchedStr, regType.type);
          input = input [matchedStr.length .. $];
          break;
        }
      }
      if (!foundMatchingRegex) {
        throw new Exception (text (`Couldn't lex `, input));
      }
    }
  }
  auto currentLineData = currentLineTokens [];
  // debug writeln (`Finished lexing a line: `, currentLineData);
  // Finished lexing a line, convert it to an expression.
  auto exprArgs = toExpressionArgs (
    currentLineData
    , scope_
  );
  if (exprArgs._is! (ExpressionArg [])) {
    auto exprArgsG = exprArgs.get! (ExpressionArg []);
    if (exprArgsG.length > 0) {
      // Don't add empty expressions.
      toRet ~= Expression (
        exprArgsG
        , Nullable!string (`_`)
      );
    }
  } else {
    return LexRet (exprArgs.get!UserError);
  }
  currentLineTokens = TokenAppender ();
  return LexRet (toRet []);
}
