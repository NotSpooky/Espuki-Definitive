// Value = (Type, InterpretedData?, Dependencies)
// Type = Primitive | Parametrized
// InterpretedData = D_int | D_long | D_customType … | Pending

// Examples:

// Interpreted constant from a literal
// valA = (LiteralInt, D_long 30, [])

// Interpreted value that will be calculated from the add rule of other variables
// valB = (I32, Pending, [addRule, input1, input2])
// The same value after computing it:
// valB = (I32, D_int 100, [addRule, input1, input2])
// The dependencies can be stripped when they aren't needed anymore.


// Computation graph:
