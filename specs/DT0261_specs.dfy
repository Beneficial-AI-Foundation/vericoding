// <vc-preamble>
// Define a Float datatype that can represent NaN for IEEE 754 compliance
datatype Float = Finite(value: real) | NaN

// Type aliases for clarity
type FloatVector = seq<Float>
type BoolVector = seq<bool>

// Predicate to check if a Float is NaN
predicate IsNaN(f: Float)
{
    f.NaN?
}

// Greater-than comparison for Float values with IEEE 754 semantics
predicate FloatGreater(x1: Float, x2: Float)
{
    match (x1, x2) {
        case (Finite(v1), Finite(v2)) => v1 > v2
        case (_, _) => false  // Any comparison involving NaN returns false
    }
}

// Main specification method for numpy.greater
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method numpy_greater(x1: FloatVector, x2: FloatVector) returns (result: BoolVector)
    // Input vectors must have the same length
    requires |x1| == |x2|
    
    // Output has the same length as inputs
    ensures |result| == |x1|
    
    // Element-wise comparison semantics: result[i] is true iff x1[i] > x2[i]
    ensures forall i :: 0 <= i < |result| ==>
        (result[i] <==> FloatGreater(x1[i], x2[i]))
    
    // Antisymmetry property: if x1[i] > x2[i] then not (x2[i] > x1[i])
    ensures forall i :: 0 <= i < |result| ==>
        (result[i] ==> !FloatGreater(x2[i], x1[i]))
    
    // IEEE 754 compliance: NaN comparisons always return false
    ensures forall i :: 0 <= i < |result| ==>
        ((IsNaN(x1[i]) || IsNaN(x2[i])) ==> result[i] == false)
    
    // Consistency with FloatGreater definition
    ensures forall i :: 0 <= i < |result| ==>
        (result[i] == FloatGreater(x1[i], x2[i]))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
