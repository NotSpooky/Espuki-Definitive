import std.algorithm;
import std.array;
import std.conv;
import std.range;
import std.stdio;
import pegged.grammar;
import pegged.tohtml; // Useful for debugging.
import pegString = pegged.examples.strings;
import pegged.examples.numbers;
import value : Value, Var;
import type;

void main () {
  // TODO: Spacing.
  mixin(grammar(`
    Program:
      Program <- Expressions :';'
      Expressions < Expression+
      Expression < Assignment
                   / LastReference
                   / StringLiteral
                   / FloatLiteral
                   / IntegerLiteral
                   / TupleLiteral
                   / Grouping
                   / ArrayLiteral
                   / Lambda
                   / TypeName
                   / InputPosReference
                   / InputNameReference
    # Scientific: (FloatLiteral / IntegerLiteral) ( ('e' / 'E' ) Integer )
      Assignment < Expression "->" identifier
      LastReference <- :'_' [0-9]*
      StringLiteral <- pegString.String
      FloatLiteral <~ Numbers.Integer ('.' Numbers.Unsigned )
      IntegerLiteral <- Numbers.Integer
      TupleLiteral <- :'(' Spacing ((Expressions Spacing :',') | (Expressions Spacing (:',' Spacing Expressions)+ Spacing :','?)) Spacing :')'
      ArrayLiteral <- :'[' Spacing ((Expressions Spacing :',')* Spacing Expressions)? Spacing :','? Spacing :']'
      Grouping < :'(' :Spacing Expressions :Spacing :')'
      Lambda < :'{' Expressions :'}'
      TypeName <~ identifier | eps
      InputPosReference <- 'in' :SingleSpacing+ IntegerLiteral
      InputNameReference <- 'in' :SingleSpacing+ identifier
      Comment <: ("/*" (!("/*" / "*/") .)* "*/")
      NestableComment <: ("/+" (NestableComment / Text)* "+/")
      Text    <: (!("/+" / "+/") .)* # Anything but begin/end markers
      SingleSpacing <- :(' ' / '\t' / '\r' / '\n' / '\r\n' / Comment / NestableComment)
      Spacing <- :(SingleSpacing)*
  `));
  string toParse =
    //`"I'm some string";`
    `("Hello", "World", 5.010);`
    //`"Sleep"->honk;`
    //`"Olis""Sleeps";`
    //`5.010;`
    //`10;`
    // `((5, 10, 10.5, "Hello") "World" ("World2",) ("LastOne"));`
    //`(_2 _3);`
    //`{5.1 /* Sleep :3 */ _34}; /+ Hello +/`
    ;
  auto parseTree = Program.Expression(toParse);
  //toHTML(parseTree, File(`spooks.html`, `w`));
  auto decimatedTree = Program.decimateTree (parseTree);
  writeln (decimatedTree);
  writeln (parseProgram (decimatedTree));
}

Value parseProgram (ParseTree pt) {
  switch (pt.name) {
    case `Program.Program`:
      assert (pt.children.length == 1);
      return parseProgram (pt[0]);
    case `Program.Expressions`:
      auto toRet = pt
        .children
        .tee !((a) { assert (a.name == `Program.Expression` ); })
        .map! (a => parseProgram (a [0]))
        .array ();
      // Temporary while rule matcher is added again.
      assert (toRet.length == 1, `TODO`);
      return toRet [0];
    case `Program.Expression`:
      assert (pt.children.length == 1);
      return parseProgram (pt[0]);
    case `Program.StringLiteral`:
      assert (pt.matches.length == 1);
      return Value (String, Var (pt.matches [0].to!string));
    case `Program.FloatLiteral`:
      assert (pt.matches.length == 1);
      return Value (Float, Var (pt.matches [0].to!float)); // TODO: Store literals as another type.
    case `Program.IntegerLiteral`:
      assert (pt.matches.length == 1);
      return Value (I64, Var (pt.matches [0].to!long));
    case `Program.TupleLiteral`:
      return (Value (
        TupleT,
        Var (pt.children.map!(a => parseProgram(a)).array)
      ));
    default:
      writeln (`> TODO: `, pt.name);
      assert (0);
  }
}

  // To avoid re-generating the grammar, use https://github.com/PhilippeSigaud/Pegged/wiki/Grammars-as-D-Modules
