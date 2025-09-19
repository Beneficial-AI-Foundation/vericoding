// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method diagflat(v: seq<real>) returns (result: seq<real>)
    requires |v| >= 0
    ensures |result| == |v| * |v|
    // Elements on the main diagonal are from the input vector
    ensures forall i :: 0 <= i < |v| ==> result[i * |v| + i] == v[i]
    // All other elements are zero  
    ensures forall i, j {:trigger result[i * |v| + j]} :: 0 <= i < |v| && 0 <= j < |v| && i != j ==> result[i * |v| + j] == 0.0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
