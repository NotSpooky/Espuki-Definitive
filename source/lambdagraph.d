import value;
import type;
import graph;
import std.algorithm;
import std.array;
import std.conv;
import pegged.grammar;
import value: FunctionTree;

Node createLambda (ParseTree [] lambdaTree) {
  // Doing this in O(n) would probably be slower.
  auto lastReferences = lambdaTree
    .filter! (child => child.name == "Program.LastReference")
    .map!(c => c.matches[0][1..$].to!uint)
    .array ()
    .sort ();
  uint last = 0;
  foreach (lastReference; lastReferences) {
    // Check that no references are missed and keep track of the last one.
    if (lastReference == last + 1) {
      last ++;
    } else if (lastReference > last + 1) {
      throw new Exception (text (
        "Missing _", last + 1, ", but found _", lastReference
      ));
    }
  }
  return Node (InterpretedValue (
    Code, Var (FunctionTree (lambdaTree [0], last))
  ));
}
