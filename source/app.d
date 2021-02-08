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
    (RTValue val) {
      writeln (val);
      // TODO: Exit with code.
    }
    , (typeof (null)) {
      writeln (`No result`);
    }
    , (UserError ue) {
      stderr.writeln (`Error `, ue.message);
      // TODO: Exit with code.
    }
  );

}
