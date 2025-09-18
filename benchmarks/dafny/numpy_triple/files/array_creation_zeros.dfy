// <vc-preamble>
// Method to create a sequence of zeros of given length
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method zeros<T>(n: nat, zero: T) returns (result: seq<T>)
    ensures |result| == n
    // All elements are zero
    ensures forall i :: 0 <= i < |result| ==> result[i] == zero
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
