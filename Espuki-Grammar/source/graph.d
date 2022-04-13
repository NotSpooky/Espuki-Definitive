module graph;
import std.sumtype;
import rule : Rule;
import type : TypeId;
import value : InterpretedValue;

struct CallNode {
  Node * [] inputs;
  Rule * rule;
  TypeId type;
}

alias Node = SumType!(CallNode, InterpretedValue);

// Not named type to prevent clashes with the type module.
TypeId typeId (Node node) {
  return node.match!(n => n.type);
}

struct SortedNode {
  Node node;
  bool [] lastReferences;
}

alias LastNodes = Node [];

  // First we parse.
  // Then we resolve references in the scope.
  // Then we find matching rules.
  // The rules are converted into nodes, this gives them input nodes and information.
  // Then topological sorting is applied.
  // Then nodes are reordered according to their priorities.
  // Then node last references are added.
  // Then optimizations are done
