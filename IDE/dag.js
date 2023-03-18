const assert = require('./utilities.js').assert;
const example = require('./example.js');

const Operations = Object.freeze({
    "execute": "execute",
    "endOfLifetime": "endOfLifetime"
});

function outputNodesToExecuteOrder (outputNodes) {
    const interpretNodes = [];
    const runtimeNodes = [];

    const interpretQueue = [];
    const runtimeQueue = [];

    // Set of already queued nodes
    const queued = new Set();

    for (let outputNode of outputNodes) {
        if (outputNode.isInterpreted) {
            interpretQueue.push(outputNode);
        } else {
            runtimeQueue.push(outputNode);
        }
    }

    while (interpretQueue.length > 0) {
        const node = interpretQueue.shift();

        // 1. Add the node to the list of nodes to interpret
        // Remove the dependencies from the node
        const toAppend = {
            operation: Operations.execute,
            // Node without dependencies
            node: node
        };

        // Add to the beginning of the list
        interpretNodes.unshift(toAppend);

        // 2. Add the list of dependencies to the list of nodes in the queue
        for (let dependency of node.dependencies) {
            // All dependencies must be interpreted
            assert.that(dependency.isInterpreted);
            interpretQueue.push(dependency);
            
            // 3. Add the end of lifetimes of the dependencies to the list of nodes to interpret
            //  3.1 If a dependency's end of lifetime is already in the list, move the dependency execution to the beginning of the list
            if (queued.has(dependency)) {
                const index = interpretNodes.findIndex((node) => {
                    // Check the id
                    return node.id === dependency.id;
                });

                // Move the node to the beginning of the list
                const node = interpretNodes.splice(index, 1);
                assert.deepEqual(node.length, 1);
                interpretNodes.unshift(node[0]);
            } else {
            //   3.2 If a dependency's end of lifetime is not in the list, add it
                queued.add(dependency);
                interpretNodes.unshift({
                    operation: Operations.endOfLifetime,
                    node: dependency
                });
            }
        }
    }

    return {
        runtimeNodes: runtimeNodes,
        interpretNodes: interpretNodes
    };
}

// Execute the interpret nodes in the order they are in the list
const interpretNodes = outputNodesToExecuteOrder([example.secondResult]).interpretNodes;

for (let node of interpretNodes) {
    //console.log(JSON.stringify(node));
    if (node.operation === Operations.execute) {
        // TODO: set places for the results?
        // Currently sets the result in the node like in example.js
        if (node.node.interpretedData === example.Pending) {
            example.interpret(node.node);
        }
        console.log("Executed: ", node.node.id);
    } else {
        assert.deepEqual(node.operation, Operations.endOfLifetime);
        console.log("Ending lifetime of", node.id);
    }
}
