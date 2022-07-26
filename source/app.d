module app;

import core.stdc.stdlib : exit;
import std.algorithm;
import std.array;
import std.file : readText;
import std.conv;
import std.range;
import std.stdio;
import std.sumtype;
import pegged.grammar;
import pegged.tohtml; // Useful for debugging.
import pegString = pegged.examples.strings;
import pegged.examples.numbers;
import graph;
import intrinsics;
import rule;
import type;
import value;

void main (string [] args) {
  // TODO: Spacing.
  mixin(grammar(`
    Program:
      Program <- (Expressions Spacing :';'? Spacing)*
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
  if (args.length <= 1) {
    stderr.writeln (`Error: No filename specified.`);
    exit(1);
  } else if (args.length >= 3) {
    stderr.writeln (`Error: Not implemented: Multiple filenames.`);
    exit(1);
  }
  auto toParse = readText (args [1]);
  RuleMatcher ruleMatcher;
  /+string toParse =
    //`"I'm some string";`
    //`"Sleep"->honk;`
    //`5.010;`
    //`10;`
    //`["hello" to "goodbye", "thank you" to "you're welcome"] as aa;`
    // TODO from here:
    //`"Olis""Sleeps";`
    //`((5, 10, 10.5, "Hello") "World" ("World2",) ("LastOne"));`
    //`(_2 _3);`
    //`{5.1 /* Sleep :3 */ _34}; /+ Hello +/`
    ;+/
  auto parseTree = Program.Program(toParse);
  //toHTML(parseTree, File(`spooks.html`, `w`));
  auto decimatedTree = Program.decimateTree (parseTree);
  //writeln (decimatedTree);
  writeln (`Last result: `, parseProgram (decimatedTree, ruleMatcher, globalRules));
}

Node parseProgram (ParseTree pt, ref RuleMatcher ruleMatcher, Rule [] rules) {
  switch (pt.name) {
    case `Program.Program`:
      Node lastResult = Node.init;
      writeln (`DEBUG: Parsed program: `, pt.children);
      foreach (expressionChain; pt.children) {
        writeln (`> DEBUG: Subexpression chain: `, expressionChain);
        lastResult = parseProgram (expressionChain, ruleMatcher, rules);
      }
      return lastResult;
    case `Program.Expressions`:
      writeln (`> > DEBUG: Parsing expressions: `, pt.children);
      auto toRet = pt
        .children
        .tee !((child) {
          assert (child.name == `Program.Expression` );
          /*
          assert (
            child.matches.length == 1
            , `Expected a single expression` // `Expected expressions to have a single element: ` ~ child.to!string
          );*/
        })
        .map! (child => parseProgram (child [0], ruleMatcher, rules))
        .array ();
      uint offsetPos = 0;
      auto retNode = Node.init;
      while (offsetPos < toRet.length) {
        // When no offset, then it hasn't been parsed yet.
        auto args = (offsetPos == 0 ? [] : [retNode]) ~ toRet [offsetPos .. $];
        writeln (`> > > DEBUG: Parsing args: `, args);
        if (args.length == 1) {
          return args [0];
        }
        // TODO: Optimize.
        auto rule = rules [ruleMatcher.match (args, rules)];
        writeln(`> > > DEBUG: Matched rule `, rule);
        if (args.all! (
          arg => arg.match! ((InterpretedValue iv) => true, (CallNode cN) => false)
        )) {
          // Can be interpreted.
          writeln (`> > > Can be interpreted!`);
          auto sentArgs = args.map!(arg => arg.tryMatch!((InterpretedValue iV) => iV)).array;
          retNode = rule.applyFun (sentArgs, ruleMatcher);
        }
        offsetPos += rule.params.length;
	/+
          .applyRule (
            args
            , []
            , ruleMatcher
          );
	+/
      }
      debug {
        writeln ("< < Returned result is ", retNode);
      }
      return retNode;
    case `Program.Expression`:
      assert (pt.children.length == 1);
      return parseProgram (pt[0], ruleMatcher, rules);
    case `Program.StringLiteral`:
      assert (pt.matches.length == 1);
      return Node(InterpretedValue (String, Var (pt.matches [0].to!string)));
    case `Program.FloatLiteral`:
      assert (pt.matches.length == 1);
      // TODO: Store literals as another type.
      return Node(InterpretedValue (F32, Var (pt.matches [0].to!float)));
    case `Program.IntegerLiteral`:
      assert (pt.matches.length == 1);
      return Node(InterpretedValue (I64, Var (pt.matches [0].to!long)));
    case `Program.TupleLiteral`:
      auto childrenVals = pt
        .children
        .map! (a => parseProgram(a, ruleMatcher, rules))
        .array;
      if (childrenVals.all!(a => a.match!((InterpretedValue i) => true, (CallNode c) => false))) {
        return Node(InterpretedValue (
          TupleT,
          Var (childrenVals.map!(a => a.tryMatch!((InterpretedValue i) => i.extractVar)).array)
        ));
      } else {
        assert (false, `TODO: Create a rule for runtime tuple creation for tuple literals.`);
      }
    case `Program.ArrayLiteral`:
      auto parsedTree = pt.children.map! ((element) {
        auto parsed = parseProgram (element, ruleMatcher, rules);
        return parsed.match!(
          (InterpretedValue iV) => Value (iV.type, iV.value.var)
          , (CallNode cN) {
            writeln (`DEB: Trying to create an array with the element `, cN);
            assert (0, `TODO: Array call nodes`);
            return Value(Any, Var(null));
          }
        );
      });
      if (parsedTree.empty) {
        return Node(InterpretedValue (
          EmptyArray, Var(Value[].init)
        ));
      } else {
        auto varToRet = new Var [parsedTree.length];
        return Node(InterpretedValue (
          arrayOf(parsedTree [0].type),
          // TODO: Store as an array of Var instead of arrays of values
          // To do so, the D type must be extracted from the Values
          Var (parsedTree.array)
        ));
      }
    case `Program.Symbol`:
      return Node(InterpretedValue (Symbol, Var (pt.matches [0])));
    default:
      writeln (`> TODO: `, pt.name);
      assert (0);
  }
}

  // To avoid re-generating the grammar, use https://github.com/PhilippeSigaud/Pegged/wiki/Grammars-as-D-Modules
