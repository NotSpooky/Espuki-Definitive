const assert = require("./utilities.js").assert;

const Types = new Set([
  "I32 Function(I32, I32)",
  "I32",
  "LiteralInt"
]);

// Pending is a symbol
const Pending = Symbol();

const valA = {
  id: 0,
  type: Types.LiteralInt,
  isInterpreted: true,
  interpretedData: 5,
  dependencies: []
};

const valB = {
  id: 1,
  type: Types.LiteralInt,
  isInterpreted: true,
  interpretedData: 30,
  dependencies: []
}

const addRule = {
  id: 2,
  type: Types[`I32 Function(I32, I32)`],
  isInterpreted: true,
  interpretedData: (a, b) => a.interpretedData + b.interpretedData,
  dependencies: []
};

let firstResult = {
  id: 3,
  type: Types.I32,
  isInterpreted: true,
  interpretedData: Pending,
  dependencies: [addRule, valA, valB]
};

let secondResult = {
  id: 4,
  type: Types.I32,
  isInterpreted: true,
  interpretedData: Pending,
  dependencies: [addRule, firstResult, valB]
};

function interpret(value) {
  assert.that(value.isInterpreted);
  assert.deepEqual(value.interpretedData, Pending);
  assert.that(value.dependencies.length > 0, "No rule to interpret");
  const rule = value.dependencies[0];
  const args = value.dependencies.slice(1);
  const result = rule.interpretedData(...args);
  value.interpretedData = result;
  // console.log("Interpreted", value, "to", result);
  return value;
}

// Test single operation.
// interpret(firstResult);
// console.log(JSON.stringify(firstResult, null, 2));

// const queue = [firstResult, secondResult];

// while (queue.length > 0) {
//   const value = queue.shift();
//   if (value.interpretedData === Pending) {
//     interpret(value);
//   }
// }

// console.log(JSON.stringify(secondResult, null, 2));
// console.log(secondResult.interpretedData);

module.exports = {
  Types,
  Pending,
  valA,
  valB,
  addRule,
  firstResult,
  secondResult,
  interpret
}
