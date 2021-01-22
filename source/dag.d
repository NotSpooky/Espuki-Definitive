module dag;
/+

import app : Type;
import std.algorithm;
import std.range;
import std.array;
import std.conv;

struct Connection {
  BaseNode owner;
  Edge * [] connectedTo;
  @disable this ();
  this (BaseNode owner, Edge * [] connectedTo) {
    this.owner = owner;
    this.connectedTo = connectedTo;
  }
}

struct TypedConnection {
  BaseNode owner;
  Edge * [] connectedTo;
  Type type;
  @disable this ();
  this (BaseNode owner, Edge * [] connectedTo, Type type) {
    this.owner = owner;
    this.connectedTo = connectedTo;
    this.type = type;
  }
}

class BaseNode {
  TypedConnection [] inputs;
  TypedConnection [] outputs;
  @disable this ();
  this (
    TypedConnection [] inputs
    , TypedConnection [] outputs
  ) {
    this.inputs = inputs;
    this.outputs = outputs;
  }
  
  auto inputNodes () {
    return this.inputs.map!`a.connectedTo`.joiner.map!`a.input`.array;
  }
  auto filledInputPositions () {
   return this.inputs
    .enumerate
    .filter! `a [1].connectedTo.length > 0`
    .map!`a [0].to!uint`
    .array;
  }
}

struct Edge {
  BaseNode input;
  uint inputPos;
  BaseNode output;
  uint outputPos;
  
  private auto inO () {
    auto toRet = input.outputs;
    assert (toRet.length > inputPos);
    return toRet [inputPos];
  }

  auto outType () {
     return inO ().type;
  }
}

struct DAG {
  BaseNode [] inputNodes; // From outside.
  BaseNode [] returnNodes; // Ditto.
  BaseNode [] consumerNodes; // From inside.
  auto toposort () {
    BaseNode [] toProcess = consumerNodes ~ returnNodes.map!(to!BaseNode).array;
    bool [Edge *] processedEdges;
    Appender!(BaseNode []) toReturn;
    while (toProcess != []) {
      auto current = toProcess [0];
      toProcess = toProcess [1..$];
      toReturn ~= current;
      foreach (inputEdge;
        current
        .inputs
        .map!`a.connectedTo`
        .joiner
        .filter!((const inputEdge) => inputEdge !in processedEdges)
      ) {
        processedEdges [inputEdge] = true;
        auto inputNode = inputEdge.input;
        if (
            inputNode
            .outputs
            .map!`a.connectedTo`
            .joiner
            .all!(a => a in processedEdges)
           ) {
          // Could remove the node's outputs from processedEdges
          // but will probably make the algorithm slower for less
          // memory usage.
          toProcess ~= inputNode;
        }
      }
    }
    return toReturn.data;
  }
}
+/
