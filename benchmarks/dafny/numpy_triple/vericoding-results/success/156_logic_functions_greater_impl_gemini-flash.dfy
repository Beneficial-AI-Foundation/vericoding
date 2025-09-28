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
/* helper modified by LLM (iteration 5): This helper function creates a new sequence of booleans of a given length. This was missing from the available API and was identified as a compilation error in the main method. */
function new_bool_sequence(length: int): BoolVector
    requires length >= 0
    ensures |new_bool_sequence(length)| == length
{
    if length == 0 then [] else new_bool_sequence(length - 1) + [false]
}
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
/* code modified by LLM (iteration 5): Changed `GetFloatGreater` to `FloatGreater` as the former was an unresolved identifier, which was causing a compilation error. */
{
  var res: BoolVector := new_bool_sequence(|x1|);
  var i := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |res| == |x1|
    invariant forall k :: 0 <= k < i ==> (res[k] <==> FloatGreater(x1[k], x2[k]))
  {
    res := res[i := FloatGreater(x1[i], x2[i])];
    i := i + 1;
  }
  return res;
}
// </vc-code>
