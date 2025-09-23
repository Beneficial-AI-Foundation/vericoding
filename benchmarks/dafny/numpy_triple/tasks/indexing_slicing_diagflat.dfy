// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method DiagFlat(v: seq<real>) returns (result: seq<seq<real>>)
  requires |v| >= 0
  ensures |result| == |v|  // Square matrix: number of rows equals input length
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == |v|  // Each row has correct length
  ensures forall i, j :: 0 <= i < |v| && 0 <= j < |v| && i == j ==> result[i][j] == v[i]  // Diagonal elements
  ensures forall i, j :: 0 <= i < |v| && 0 <= j < |v| && i != j ==> result[i][j] == 0.0  // Off-diagonal elements are zero
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
