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
  result := [];
  var i := 0;
  while i < |v|
    invariant 0 <= i <= |v|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> |result[k]| == |v|
    invariant forall k, j :: 0 <= k < i && 0 <= j < |v| && k == j ==> result[k][j] == v[k]
    invariant forall k, j :: 0 <= k < i && 0 <= j < |v| && k != j ==> result[k][j] == 0.0
  {
    var row := [];
    var j := 0;
    while j < |v|
      invariant 0 <= j <= |v|
      invariant |row| == j
      invariant forall l :: 0 <= l < j && l == i ==> row[l] == v[i]
      invariant forall l :: 0 <= l < j && l != i ==> row[l] == 0.0
    {
      if j == i {
        row := row + [v[i]];
      } else {
        row := row + [0.0];
      }
      j := j + 1;
    }
    result := result + [row];
    i := i + 1;
  }
}
// </vc-code>
