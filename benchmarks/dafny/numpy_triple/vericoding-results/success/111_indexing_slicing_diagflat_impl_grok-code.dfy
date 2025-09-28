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
  /* code modified by LLM (iteration 2): added loop invariants to prove postconditions for diagonal matrix construction */
  var matrix: seq<seq<real>> := [];
  for i := 0 to |v|
    invariant |matrix| == i
    invariant forall k :: 0 <= k < i ==> |matrix[k]| == |v|
    invariant forall k, l :: 0 <= k < i && 0 <= l < |v| && k != l ==> matrix[k][l] == 0.0
    invariant forall k, l :: 0 <= k < i && 0 <= l < |v| && k == l ==> matrix[k][l] == v[k]
  {
    var row: seq<real> := [];
    for j := 0 to |v|
      invariant |row| == j
      invariant forall m :: 0 <= m < j && m != i ==> row[m] == 0.0
      invariant forall m :: 0 <= m < j && m == i ==> row[m] == v[i]
    {
      if i != j {
        row := row + [0.0];
      } else {
        row := row + [v[i]];
      }
    }
    matrix := matrix + [row];
  }
  result := matrix;
}
// </vc-code>
