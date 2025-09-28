// <vc-preamble>
// Method to compute the outer product of two vectors
// Given vectors a and b, produces a matrix where result[i][j] = a[i] * b[j]
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added bounds checking for array indices */
function outerHelper(i: int, j: int, a: seq<real>, b: seq<real>): real
  requires 0 <= i < |a|
  requires 0 <= j < |b|
{
  a[i] * b[j]
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
/* code modified by LLM (iteration 5): added bounds checking for outerHelper calls */
{
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> |result[k]| == |b|
    invariant forall k, l :: 0 <= k < i && 0 <= l < |b| ==> result[k][l] == outerHelper(k, l, a, b)
  {
    var row : seq<real> := [];
    var j := 0;
    while j < |b|
      invariant 0 <= j <= |b|
      invariant |row| == j
      invariant forall l :: 0 <= l < j ==> row[l] == outerHelper(i, l, a, b)
    {
      row := row + [outerHelper(i, j, a, b)];
      j := j + 1;
    }
    result := result + [row];
    i := i + 1;
  }
}
// </vc-code>
