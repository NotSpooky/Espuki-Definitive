module app;

import std.stdio;
import execute;

void main (string [] args) {
  if (args.length != 2) {
    stderr.writeln (`Usage: espuki file.es`);
    return;
  }
  import std.algorithm;
  import std.conv : to;
  import mir.algebraic : visit;
  auto result = executeFromLines (File (args [1]).byLineCopy ());
  result.visit! (
    (RTValue val) { writeln (val); }
    , (UserError ue) {
      stderr.writeln (`Error `, ue.message);
    }
  );
}
