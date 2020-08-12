module parser;

import std.conv;
import std.range;

struct Token {
  string strVal;
  enum Type {
    comma
    , dot
    , minus
    , openingBracket
    , closingBracket
    , openingParenthesis
    , closingParenthesis
    , openingSquareBracket
    , closingSquareBracket
    , floatLiteral
    , integerLiteral
    , stringLiteral
    , singleQuotSymbol
    , identifier
    , backslash // Handled internally
  }
  Type type;
}

debug import std.stdio;

import std.typecons;
alias LexRet = Nullable!(Token [][]);
import std.algorithm;
// Mutable mess :)
auto lex (R)(R inputLines) {
  Appender!(Token [][]) toRet;
  // Outside the loop as output lines might not have a 1:1 relationship with
  // input lines in cases such as empty/commented lines or '\' at the end of
  // a line.
  Appender!(Token []) currentLineTokens;
  bool inAsteriskComment = false;
  uint plusCommentDepth = 0;

  import std.array;
  import std.string;

  lexLine: // Might be better to include popFront here.
  for (; !inputLines.empty; inputLines.popFront) {
    auto line = inputLines.front;
    writeln ("\tLexing line ", line);

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
    }
    while (!line.empty) {
      line = line.stripLeft ();
      if (line.empty) {
        // Ignore empty lines.
        break;
      }
      Nullable!(Token.Type) type;
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
          case '-':
            type = minus;
            break;
          default:
            break;
        }
        if (!type.isNull ()) {
          // Was a single-character token.
          currentLineTokens ~= Token (line.front.to!string, type.get ());
          line.popFront ();
        } else {
          if (line.startsWith (`//`)) {
            // Might be better to strip comments in the caller
            // Because we also need to check things such as \ at the end of line.
            break;
          } else if (line.startsWith (`/*`)) {
            inAsteriskComment = true;
            auto toReposition = line [2..$].countUntil (`*/`);
            if (toReposition >= 0) {
              inAsteriskComment = false;
              line = line [toReposition + `/**/`.length .. $]; 
              continue;
            } else {
              // Comment doesn't end on this line.
              inputLines.popFront ();
              goto lexLine;
            }
          } else if (line.startsWith (`/+`)) {
            plusCommentDepth ++;
            assert (0, `TODO: Nestable comments`);
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
                //writeln (`Finished string :D`);
                auto len = line.length - inputToUse.length + 1;
                currentLineTokens ~= Token (line [0 .. len], stringLiteral);
                line = line.drop (len);
                break;
              } else {
                //writeln (`Normal character: `, inputToUse.front);
                // Single non-escaped character
                inputToUse.popFront ();
              }
            }
          }
          enum regexTypes = [
            RegexType (ctRegex!`^[0-9]+\.[0-9]+`, floatLiteral)
            , RegexType (ctRegex!`^[0-9]+`, integerLiteral)
            , RegexType (ctRegex!`^[\w]+`, identifier)
            , RegexType (ctRegex!`^'[\w]+`, singleQuotSymbol)
            , RegexType (ctRegex!`^\\`, backslash)
          ];
          foreach (regType; regexTypes) {
            auto matched = line.matchFirst (regType.regexS);
            if (!matched.empty) {
              auto matchedStr = matched.front;
              currentLineTokens ~= Token (matchedStr, regType.type);
              line = line [matchedStr.length .. $];
              break;
            }
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
        stderr.writeln (`Last line has \ at the end`);
        return LexRet ();
      }
      currentLineTokens = appender (currentLineData [0..$-1]);
      writeln (`currentLineData is `, currentLineData);
      continue;
    }
    debug writeln (`Token line `, currentLineData);
    toRet ~= currentLineData;
    currentLineTokens.clear ();
  }
  if (inAsteriskComment) {
    // TODO: Keep track of comment start.
    stderr.writeln (`EOF reached but /* comment wasn't closed`);
    return LexRet ();
    //throw new Exception (`Non-closed asterisk comment`);
  }
  return nullable (toRet []);
}

/+
void main () {
  writeln (lex ("  , [ ] . . .. _owo, 1234 -23 1.03"));
  writeln (lex (`hola "mundo" "uwu"`));
}+/
