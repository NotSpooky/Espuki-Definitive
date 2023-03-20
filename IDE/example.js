const assert = require("./utilities.js").assert;
const intrinsics = require("./intrinsics.js");

const valA = {
  id: 0,
  type: intrinsics.Types.LiteralInt,
  isInterpreted: true,
  interpretedData: 5,
  dependencies: []
};

const valB = {
  id: 1,
  type: intrinsics.Types.LiteralInt,
  isInterpreted: true,
  interpretedData: 30,
  dependencies: []
}

const addRule = {
  id: 2,
  type: intrinsics.Types[`I32 Function(I32, I32)`],
  isInterpreted: true,
  interpretedData: (a, b) => (a + b) | 0,
  dependencies: []
};

let firstResult = {
  id: 3,
  type: intrinsics.Types.I32,
  isInterpreted: true,
  dependencies: [addRule, valA, valB]
};

let secondResult = {
  id: 4,
  type: intrinsics.Types.I32,
  isInterpreted: true,
  dependencies: [addRule, firstResult, valB]
};

const exampleDag = {
  0: valA,
  1: valB,
  2: addRule,
  3: firstResult,
  4: secondResult,
};

module.exports = {
  valA,
  valB,
  addRule,
  firstResult,
  secondResult,
  exampleDag,
}
