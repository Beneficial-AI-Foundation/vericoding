// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function CreateRow(v: seq<real>, rowIndex: int): seq<real>
  requires 0 <= rowIndex < |v|
  ensures |CreateRow(v, rowIndex)| == |v|
  ensures forall j :: 0 <= j < |v| ==> 
    CreateRow(v, rowIndex)[j] == if j == rowIndex then v[rowIndex] else 0.0
{
  if |v| == 0 then []
  else if |v| == 1 then [if rowIndex == 0 then v[0] else 0.0]
  else if rowIndex == 0 then [v[0]] + seq(|v| - 1, _ => 0.0)
  else seq(|v|, j => if j == rowIndex then v[rowIndex] else 0.0)
}
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
    var row := CreateRow(v, i);
    result := result + [row];
    i := i + 1;
  }
}
// </vc-code>
