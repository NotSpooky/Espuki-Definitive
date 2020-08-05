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
  }
  Type type;
}

debug import std.stdio;

// Ignores comments.
auto lex (string input) {
  import std.array;
  import std.typecons;
  import std.string;
  Appender!(Token []) toRet;
  while (!input.empty) {
    input = input.stripLeft ();
    if (input.empty) {
      break;
    }
    Nullable!(Token.Type) type;
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
        case '-':
          type = minus;
          break;
        default:
          break;
      }
      if (!type.isNull ()) {
        // Was a single-character token.
        toRet ~= Token (input.front.to!string, type.get ());
        input.popFront ();
      } else {
        // Multi-character token.
        import std.regex;
        struct RegexType {
          alias CTReg = typeof (ctRegex!``);
          CTReg regexS;
          Token.Type type;
        }
        if (input.front == '"') {
          auto inputToUse = input [1..$];
          while (true) {
            if (inputToUse.startsWith (`\\`) || inputToUse.startsWith (`\"`)) {
              //writeln (`Escaped token`);
              inputToUse = inputToUse.drop (2);
            } else if (inputToUse.empty) {
              throw new Exception (`Reached end of line without closing string literal`);
            } else if (inputToUse.front == '"') {
              //writeln (`Finished string :D`);
              auto len = input.length - inputToUse.length + 1;
              toRet ~= Token (input [0 .. len], stringLiteral);
              input = input.drop (len);
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
        ];
        foreach (regType; regexTypes) {
          auto matched = input.matchFirst (regType.regexS);
          if (!matched.empty) {
            auto matchedStr = matched.front;
            toRet ~= Token (matchedStr, regType.type);
            input = input [matchedStr.length .. $];
            break;
          }
        //assert (0, `TODO`);
        }
      }
    }
  }
  return toRet.data;
}

void main () {
  writeln (lex ("  , [ ] . . .. _owo, 1234 -23 1.03"));
  writeln (lex (`hola "mundo" "uwu"`));
}
