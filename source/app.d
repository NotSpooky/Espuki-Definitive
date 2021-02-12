module app;

import std.stdio;
import execute;
import mir.algebraic;
import std.algorithm;

void main (string [] args) {
  if (args.length != 2) {
    stderr.writeln (`Usage: espuki file.es`);
    return;
  }
  import std.conv : to;
  import test : executeFromFile;
  auto result = executeFromFile (args [1]);
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

