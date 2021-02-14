module lexer;

import std.conv;
import std.range;

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
    , typeIdentifier        // For types, starts with uppercase
    , underscoreIdentifier  // _[0-9]+ has special meaning in this language
    , colon
    , semicolon             // Outside of this module, this shouldn't appear
    , backslash             // Ditto
    , rightArrow
    , verticalLine          // Used for sumtypes
  }
  Type type;
}

debug import std.stdio;

import mir.algebraic;
import std.algorithm;
import execute : RTValue, UserError, ValueScope;

import parser : Expression, ExpressionArg, toExpressionArgs;
alias LexRet = Variant! (Expression [], UserError);

import std.algorithm;
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
  bool inAsteriskComment = false;
  uint plusCommentDepth = 0;

  import std.array;
  import std.string;

  // Note: Jumping to this label doesn't execute a popFront at the start.
  lexLine:
  for (; !inputLines.empty; inputLines.popFront) {
    auto line = inputLines.front;

    continueLine:

    // Comment handling
    if (inAsteriskComment) {
      assert (
        plusCommentDepth == 0
        , `Shouldn't be in 2 comment types at the same time`
      );
      if (line.findSkip (`*/`)) {
        inAsteriskComment = false;
      } else {
        // Comment didn't finish on this line.
        continue;
      }
    } else if (plusCommentDepth > 0) {
      while (true) {
        if (line.startsWith (`+/`) || line.startsWith (`/+`)) {
          assert (line.length >= 2);
          if (line.front == '+') { // Is +/
            plusCommentDepth --;
            line = line [2..$];
            if (plusCommentDepth == 0) {
              goto continueLine;
            }
          } else { // Is /+
            assert (line.front == '/');
            plusCommentDepth ++;
            line = line [2..$];
          }
        } else if (line.empty) {
          // Comment didn't finish on this line.
          inputLines.popFront ();
          goto lexLine;
        } else {
          // Didn't match boundary: still inside comment.
          line.popFront;
        }
      }
    }
    while (!line.empty) {
      line = line.stripLeft ();
      if (line.empty) {
        // Ignore empty lines.
        break;
      }
      Nullable! (Token.Type) type;
      with (Token.Type) {
        switch (line.front) {
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
              line.popFront ();
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
              goto continueLine;
            }
          default:
            break;
        }
        if (!type.isNull ()) {
          // Was a single-character token.
          currentLineTokens ~= Token (line.front.to!string, type.get ());
          line.popFront ();
        } else {
          if (line.startsWith (`->`)) {
            currentLineTokens ~= Token (line [0..2], Token.Type.rightArrow);
            line = line [2..$];
            goto continueLine;
          } else if (line.startsWith (`//`)) {
            // Might be better to strip comments in the caller
            // Because we also need to check things such as \ at the end of line.
            break;
          } else if (line.startsWith (`/*`)) {
            inAsteriskComment = true;
            line = line [2..$];
            goto continueLine;
          } else if (line.startsWith (`/+`)) {
            plusCommentDepth ++;
            line = line [2..$];
            goto continueLine;
          }
          // Multi-character token.
          import std.regex;
          struct RegexType {
            alias CTReg = typeof (ctRegex!``);
            CTReg regexS;
            Token.Type type;
          }
          if (line.front == '"') {
            auto inputToUse = line [1..$];
            while (true) {
              if (inputToUse.startsWith (`\\`) || inputToUse.startsWith (`\"`)) {
                //writeln (`Escaped token`);
                inputToUse = inputToUse.drop (2);
              } else if (inputToUse.empty) {
                assert (0, `TODO: Multi-line string literals`);
              } else if (inputToUse.front == '"') {
                auto len = line.length - inputToUse.length + 1;
                currentLineTokens ~= Token (line [1 .. len -1], stringLiteral);
                line = line.drop (len);
                break;
              } else {
                //writeln (`Normal character: `, inputToUse.front);
                // Single non-escaped character
                inputToUse.popFront ();
              }
            }
            goto continueLine;
          }
          enum regexTypes = [
            RegexType (ctRegex!`^(?:\-?[0-9]+)\.[0-9]+`, floatLiteral)
            , RegexType (ctRegex!`^[0-9]+`, integerLiteral)
            /+, RegexType (ctRegex!`^\p{Ll}[\w]*`, identifier)
            , RegexType (ctRegex!`^\p{Lu}[\w]+`, typeIdentifier) +/
            , RegexType (ctRegex!`^\_[0-9]*`, underscoreIdentifier)
            , RegexType (ctRegex!`^\+|\-|\*|\/|(?:\w+)`, identifier)
            , RegexType (ctRegex!`^\\`, backslash) // Might be better to handle above
          ];
          bool foundMatchingRegex = false;
          foreach (regType; regexTypes) {
            auto matched = line.matchFirst (regType.regexS);
            if (!matched.empty) {
              foundMatchingRegex = true;
              auto matchedStr = matched.front;
              currentLineTokens ~= Token (matchedStr, regType.type);
              line = line [matchedStr.length .. $];
              break;
            }
          }
          if (!foundMatchingRegex) {
            return LexRet (UserError (text (`Couldn't lex `, line)));
          }
        }
      }
    }

    auto currentLineData = currentLineTokens [];
    if (currentLineData.length == 0) {
      continue;
    }
    if (currentLineData [$-1].type == Token.Type.backslash) {
      if (inputLines.empty) {
        return LexRet (UserError (`Last line has \ at the end`));
      }
      currentLineTokens = appender (currentLineData [0..$-1]);
      continue;
    }
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
  }
  if (inAsteriskComment) {
    // TODO: Keep track of comment start.
    return LexRet (UserError (`EOF reached but /* comment wasn't closed`));
  }
  return LexRet (toRet []);
}
