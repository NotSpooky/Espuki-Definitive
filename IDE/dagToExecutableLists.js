const assert = require('./utilities.js').assert;
const example = require('./example.js');

/**
 * Performs a topological sort on a directed acyclic graph (DAG).
 * @param {Array} entryNodes - An array of nodes with no incoming edges.
 * @return {Array} A sorted array of node IDs.
 */
function topologicalSort(entryNodes) {
  const visited = new Set(); // Keeps track of visited nodes
  const lifetimesEnded = new Set(); // Keeps track of nodes whose lifetimes have ended
  const result = []; // Stores the sorted node IDs

  // Helper function to perform a depth-first search on the graph
  function visit(node) {
    // Check if the node has already been visited, and return if it has
    if (visited.has(node.id)) return;

    let endedLifetimes = [];
    // Mark the node as visited

    visited.add(node.id);
    // Recursively visit each dependency of the current node
    for (const dependency of node.dependencies) {
      if (!lifetimesEnded.has(dependency.id)) {
        lifetimesEnded.add(dependency.id);
        endedLifetimes.push(dependency.id);
      }
    }

    for (const dependency of node.dependencies) {
      visit(dependency);
    }

    assert.that(node.isInterpreted, "Node not interpreted");
    // Add the current node ID to the result after all its dependencies have been visited
    result.push({
      id: node.id,
      endedLifetimes: endedLifetimes,
      outputType: node.type
    });
  }

  // Visit each entry node to perform the topological sort
  for (const entryNode of entryNodes) {
    visit(entryNode);
  }

  return result;
}

module.exports = topologicalSort;
// To call the function, use the following code:
// const topologicalSort = require('./dagToExecutableLists.js');
// const sortedNodes = topologicalSort(entryNodes);
