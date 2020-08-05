module parser;

import std.conv;

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
    , stringLiteral
    , integerLiteral
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
        default:
          break;
      }
      if (!type.isNull ()) {
        // Was a single-character token.
        toRet ~= Token (input.front.to!string, type.get ());
        input = input [1 .. $];
      } else {
        // Multi-character token.
        import std.regex;
        struct RegexType {
          alias CTReg = typeof (ctRegex!``);
          CTReg regexS;
          Token.Type type;
        }
        enum regexTypes = [
          RegexType (ctRegex!`^[0-9]+`, comma)
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
  writeln (lex ("  , [ ] . . .. _owo, 1234"));
}
