// <vc-preamble>
// Method to compute the outer product of two vectors
// Given vectors a and b, produces a matrix where result[i][j] = a[i] * b[j]
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): [Helper method to generate one row of the outer product] */
method CreateRow(i: int, a: seq<real>, b: seq<real>) returns (row: seq<real>)
  requires 0 <= i < |a|
  requires |b| >= 0
  ensures |row| == |b|
  ensures forall j :: 0 <= j < |b| ==> row[j] == a[i] * b[j]
{
  row := [];
  var j := 0;
  while j < |b|
    invariant 0 <= j <= |b|
    invariant |row| == j
    invariant forall l :: 0 <= l < j ==> row[l] == a[i] * b[l]
  {
    row := row + [a[i] * b[j]];
    j := j + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method outer(a: seq<real>, b: seq<real>) returns (result: seq<seq<real>>)
  requires |a| >= 0
  requires |b| >= 0
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == |b|
  ensures forall i, j :: 0 <= i < |a| && 0 <= j < |b| ==> result[i][j] == a[i] * b[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): [Reworked using a loop and helper method to avoid comprehension issues] */
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> |result[k]| == |b|
    invariant forall k, l :: 0 <= k < i && 0 <= l < |b| ==> result[k][l] == a[k] * b[l]
  {
    var new_row := CreateRow(i, a, b);
    result := result + [new_row];
    i := i + 1;
  }
}
// </vc-code>
