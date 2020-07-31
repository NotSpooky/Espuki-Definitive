import std.stdio;
import std.variant;
import std.algorithm;
import std.range;
import std.conv : to;
import std.typecons : Nullable, nullable;

private uint lastTypeId;
struct Type {
  //@disable this (); // Cannot disable when assigning to Variant :(
  uint id;
  string name; // Just for pretty printing.
  this (string name) {
    this.name = name;
    this.id = lastTypeId;
    lastTypeId ++;
  }
  bool opEquals()(auto ref const Type other) const {
    return other.id == this.id;
  }
}

string names (Type [] args) {
  return args.map!`a.name`.joiner.to!string;
}

struct CompositeType {
  uint parameterAmount;
  string name; // Just for pretty printing.
  this (uint parameterAmount, string name) {
    this.parameterAmount = parameterAmount;
    this.name = name;
  }

  auto instance (Type [] args) {
    // TODO: Can see if already instanced to avoid copies.
    assert (args.length == parameterAmount);
    return Type (this.name ~ ' ' ~ args.names);
  }
  auto curry (Type [] args) {
    // TODO: Can see if already instanced to avoid copies.
    assert (args.length <= parameterAmount);
    return CompositeType (
      (args.length - parameterAmount).to!uint
      , this.name ~ ' ' ~ args.names
    );
  }
}

alias TypeOrString = Algebraic!(Type, string);
alias ValueOrErr = Nullable!Value;
alias ApplyFun = ValueOrErr delegate (Value [] apply);
struct Rule {
  @disable this ();
  TypeOrString [] args;
  // Can assume that execute has correct arg types.
  ApplyFun execute;
  this (TypeOrString [] args, ApplyFun execute) {
    this.args = args;
    this.execute = execute;
  }
}

Type String;
static this () {
  String = Type (`String`);
}
struct Scope {
  @disable this ();
  Rule [] rules;
  this (Rule [] rules) {
    this.rules = rules;
  }

  ValueOrErr execute (Value [] args) {
    auto validMatches = rules.filter!((rule) {
      if (rule.args.length != args.length) return false;
      return args.zip (rule.args).all!((pair) {
        auto arg = pair [0];
        auto ruleArg = pair [1];
        if (ruleArg.type == typeid (string)) {
          // In case of strings, make sure the value has the same string
          return arg.type == String && arg.value.get!string == ruleArg.get!string;
        } else {
          assert (ruleArg.type == typeid (Type));
          return arg.type == ruleArg.get!Type;
        }
      });
    }).array;
    if (validMatches.length == 0) {
      stderr.writeln (`No valid rule for `, args);
      return ValueOrErr ();
    } else if (validMatches.length > 1) {
      stderr.writeln (
        `Multiple matching rules for `
        , args
        , validMatches.map!`"\n\t" ~ a.to!string`.joiner ()
      );
      return ValueOrErr ();
    }
    return rules [0].execute (args);
  }
}

struct Value {
  Type type;
  Variant value;
  this (Type type, Variant value) {
    this.type = type;
    this.value = value;
  }
  void toString (scope void delegate (const (char)[]) sink) {
    sink (type.name);
    sink (` `);
    sink (value.toString ());
  }
}

// OLD ESPUKI

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

void main()
{
  auto TypeT = Type (`Type`);
  auto I32 = Type (`I32`);
  auto Enum = CompositeType (2, `Enum`);
  auto exampleStruct = ["strField" : String, "intField" : I32];
  auto NameType = Enum.instance ([String, TypeT]);
  auto ExampleStruct = Type (`ExampleStruct`);
  auto construct = Rule (
    [TypeOrString ("construct"), TypeOrString (NameType)]
    , (Value [] args){
      auto namedArgs = args [1].value;
      return ValueOrErr (Value (ExampleStruct, namedArgs));
    }
  );
  auto globalScope = Scope ([construct]);
  auto strLiteral = Value (String, Variant ("Example string"));
  auto intLiteral = Value (I32, Variant (34));
  auto inputArg = Value (NameType, Variant (
    [
      Value (String, Variant ("strField")) : strLiteral
      , Value (String, Variant ("intField")) : intLiteral
    ]
  ));
  globalScope.execute (
    [Value (String, Variant ("construct")), inputArg]
  ).writeln;
}
