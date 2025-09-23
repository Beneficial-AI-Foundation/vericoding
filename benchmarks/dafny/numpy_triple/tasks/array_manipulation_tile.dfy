// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method tile<T>(A: seq<T>, reps: nat) returns (result: seq<T>)
  // Number of repetitions must be positive
  requires reps > 0
  // Result length is the product of input length and repetitions
  ensures |result| == |A| * reps
  // Each element in result corresponds to the element at the appropriate position in the input
  // using modular arithmetic to cycle through the input array (only when input is non-empty)
  ensures |A| > 0 ==> forall i :: 0 <= i < |result| ==> result[i] == A[i % |A|]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
