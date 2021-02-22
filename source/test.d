module test;

import mir.algebraic;
import std.stdio;
import execute;

auto executeFromFile (string path) {
  return executeFromLines (File (path).byLineCopy ());
}

private auto testFile (string path) {
  auto toRet = executeFromFile (path);
  if (toRet._is!RTValue) {
    return Nullable!RTValue (toRet.get!RTValue);
  } else {
    assert (toRet.isNull ());
    return Nullable!RTValue (null);
  }
}

unittest {
  import intrinsics;
  assert (testFile (`./examples/addrule.es`) == RTValue (I32, Var (7)));
  auto arrOfInt = arrayOf (I32);
  assert (testFile (`./examples/array.es`) == RTValue (
    arrOfInt, Var ([Var (1), Var (2), Var (3), Var (4), Var (5)]))
  );
  assert (testFile (`./examples/example.es`) == RTValue (I32, Var (18)));
  assert (testFile (`./examples/hello.es`) == RTValue (String, Var (`Hello world`)));
  debug writeln (`TODO: Test struct creation`);
  auto st = sumTypeOf ([
    RTValue (Kind, Var (I32))
    , RTValue (Kind, Var (F32))
    , RTValue (Kind, Var (String))
  ]);
  assert (testFile (`./examples/sumtype.es`) == RTValue (st, Var (5.1)));
  assert (testFile (`./examples/tuple.es`) == RTValue (I32, Var (4)));
}
