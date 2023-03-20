const assert = require('./utilities.js').assert;
const example = require('./example.js');
const topologicalSort = require('./dagToExecutableLists.js');

function interpretSortedNode(value, dag) {
  const node = dag[value.id];
  if (node.dependencies.length > 0) {
    const rule = node.dependencies[0];
    let args = node.dependencies.slice(1);
    // Obtain the interpretedData of the args
    args = args.map(arg => arg.interpretedData);
    const result = rule.interpretedData(...args);
    console.log("Result is " + result);
    node.interpretedData = result;
  } else {
    console.log("Literal is " + node.interpretedData);
  }

  // Delete the nodes with ended lifetimes
  for (const id of value.endedLifetimes) {
    delete dag[id];
  }
}

/**
  * @param {Object} dag MUTATED
  * @param {Object} outputs
  * @return {Object} results
  */
function interpretDag(dag, outputs) {
  console.log("Interpreting DAG");
  const sortedNodes = topologicalSort(outputs.map(output => dag[output]));
  let results = {};

  // This leaves the results in the node's interpretedData field
  for (const node of sortedNodes) {
    // Mutates node
    interpretSortedNode(node, dag);
  }

  for (const output of outputs) {
    results[output] = dag[output].interpretedData;
  }

  // Only the result nodes should remain
  assert.deepEqual(
    // Result amount
    Object.keys(results).length,
    outputs.length,
    `Expected ${outputs.length} outputs, but got ${results.length}`
  );

  // Delete the remaining nodes
  for (const id in dag) {
    delete dag[id];
  }

  return results;
}

console.log(example.secondResult.id);
const results = interpretDag(example.exampleDag, [example.secondResult.id]);
console.log("Results are");
console.log(results);
