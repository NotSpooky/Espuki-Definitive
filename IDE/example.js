function assert(x, message="No message") {
  if (!x) throw new Error("Assertion failed: " + message);
}

const Types = new Set([
  "I32 Function(I32, I32)",
  "I32",
  "LiteralInt"
]);

// Pending is a symbol
const Pending = Symbol();

const valA = {
  type: Types.LiteralInt,
  isInterpreted: true,
  interpretedData: 5,
  dependencies: []
};

const valB = {
  type: Types.LiteralInt,
  isInterpreted: true,
  interpretedData: 30,
  dependencies: []
}

const addRule = {
  type: Types[`I32 Function(I32, I32)`],
  isInterpreted: true,
  interpretedData: (a, b) => a.interpretedData + b.interpretedData,
  dependencies: []
};

let result = {
  type: Types.I32,
  isInterpreted: true,
  interpretedData: Pending,
  dependencies: [addRule, valA, valB]
};

function interpret(value) {
  assert(value.isInterpreted);
  assert(value.interpretedData === Pending, "Interpreted data should be pending");
  assert(value.dependencies.length > 0, "No rule to interpret");
  const rule = value.dependencies[0];
  const args = value.dependencies.slice(1);
  const result = rule.interpretedData(...args);
  value.interpretedData = result;
  // console.log("Interpreted", value, "to", result);
  return value;
}

interpret(result);

console.log(JSON.stringify(result, null, 2));

