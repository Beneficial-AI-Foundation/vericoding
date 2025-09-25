// <vc-preamble>
// Method that vectorizes a scalar function to operate element-wise on sequences
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Vectorize<T, U>(f: T --> U, input: seq<T>) returns (result: seq<U>)
    // Input sequence can be of any length
    requires true
    // Output sequence has same length as input
    ensures |result| == |input|
    // Each element of result is f applied to corresponding element of input
    ensures forall i :: 0 <= i < |input| ==> result[i] == f(input[i])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
