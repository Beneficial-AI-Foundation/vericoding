// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes to logic, just adding required comment. */
function CreateRow(row_index: int, total_len: nat, value: real): (result: seq<real>)
  requires 0 <= row_index < total_len
  ensures |result| == total_len
  ensures forall j :: 0 <= j < total_len ==> result[j] == (if j == row_index then value else 0.0)
{
  seq(total_len, j => if j == row_index then value else 0.0)
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
  /* code modified by LLM (iteration 5): Replaced seq comprehension with a while loop to resolve a compiler index-out-of-range error. */
  var i: nat := 0;
  result := [];
  while i < |v|
    invariant 0 <= i <= |v|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> |result[k]| == |v|
    invariant forall k, j :: 0 <= k < i && 0 <= j < |v| ==> result[k][j] == (if k == j then v[k] else 0.0)
  {
    var row := CreateRow(i, |v|, v[i]);
    result := result + [row];
    i := i + 1;
  }
}
// </vc-code>
