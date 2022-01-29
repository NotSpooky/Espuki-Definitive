module app;

import std.algorithm;
import std.array;
import std.conv;
import std.range;
import std.stdio;
import std.sumtype;
import pegged.grammar;
import pegged.tohtml; // Useful for debugging.
import pegString = pegged.examples.strings;
import pegged.examples.numbers;
import intrinsics;
import rule;
import type;
import value;

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
                   / InputPosReference
                   / InputNameReference
                   / Symbol
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
      InputPosReference <- 'in' :SingleSpacing+ IntegerLiteral
      InputNameReference <- 'in' :SingleSpacing+ identifier
      Comment <: ("/*" (!("/*" / "*/") .)* "*/")
      NestableComment <: ("/+" (NestableComment / Text)* "+/")
      Text    <: (!("/+" / "+/") .)* # Anything but begin/end markers
      SingleSpacing <- :(' ' / '\t' / '\r' / '\n' / '\r\n' / Comment / NestableComment)
      Spacing <- :(SingleSpacing)*
      Symbol <- identifier
  `));
  RuleMatcher ruleMatcher;
  string toParse =
    //`"I'm some string";`
    //`("Hello", "World", 5.010);`
    //`["First", "Second", "Third"];`
    //`"Sleep"->honk;`
    //`5.010;`
    //`10;`
    `["hello" to "goodbye", "thank you" to "you're welcome"];`
    // TODO from here:
    //`"Olis""Sleeps";`
    //`((5, 10, 10.5, "Hello") "World" ("World2",) ("LastOne"));`
    //`(_2 _3);`
    //`{5.1 /* Sleep :3 */ _34}; /+ Hello +/`
    ;
  auto parseTree = Program.Expression(toParse);
  //toHTML(parseTree, File(`spooks.html`, `w`));
  auto decimatedTree = Program.decimateTree (parseTree);
  writeln (decimatedTree);
  writeln (parseProgram (decimatedTree, ruleMatcher, globalRules));
}

Value parseProgram (ParseTree pt, ref RuleMatcher ruleMatcher, Rule [] rules) {
  switch (pt.name) {
    case `Program.Program`:
      assert (pt.children.length == 1);
      return parseProgram (pt[0], ruleMatcher, rules);
    case `Program.Expressions`:
      auto toRet = pt
        .children
        .tee !((child) {
          assert (child.name == `Program.Expression` );
          assert (
            child.matches.length == 1
            , `Expected expressions to have a single element: ` ~ child.to!string
          );
        })
        .map! (child => parseProgram (child [0], ruleMatcher, rules))
        .array ();
      return ruleMatcher.match (toRet, rules).apply (
        toRet, [], ruleMatcher
      );
    case `Program.Expression`:
      assert (pt.children.length == 1);
      return parseProgram (pt[0], ruleMatcher, rules);
    case `Program.StringLiteral`:
      assert (pt.matches.length == 1);
      return Value (String, Var (pt.matches [0].to!string));
    case `Program.FloatLiteral`:
      assert (pt.matches.length == 1);
      return Value (F32, Var (pt.matches [0].to!float)); // TODO: Store literals as another type.
    case `Program.IntegerLiteral`:
      assert (pt.matches.length == 1);
      return Value (I64, Var (pt.matches [0].to!long));
    case `Program.TupleLiteral`:
      return (Value (
        TupleT,
        Var (pt.children.map! (a => parseProgram(a, ruleMatcher, rules)).array)
      ));
    case `Program.ArrayLiteral`:
      auto parsedTree = pt.children.map! (element => parseProgram (element, ruleMatcher, rules)).array;
      if (parsedTree.length == 0) {
        return Value (
          EmptyArray, Var(Value[].init)
        );
      } else {
        auto varToRet = new Var [parsedTree.length];
        return Value (
          ArrayOf(parsedTree [0].type),
          // TODO: Store as an array of Var instead of arrays of values
          // To do so, the D type must be extracted from the Values
          Var (parsedTree.map!(a =>
            a.value.tryMatch!((VarWrapper a) => a.var)
          ).array)
        );
      }
    case `Program.Symbol`:
      writeln (`Got symbol: `, pt);
      return Value (Symbol, Var (pt.matches [0]));
    default:
      writeln (`> TODO: `, pt.name);
      assert (0);
  }
}

  // To avoid re-generating the grammar, use https://github.com/PhilippeSigaud/Pegged/wiki/Grammars-as-D-Modules
