// <vc-preamble>
// Method to compute the outer product of two vectors
// Given vectors a and b, produces a matrix where result[i][j] = a[i] * b[j]
// </vc-preamble>

// <vc-helpers>

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
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> |result[k]| == |b|
    invariant forall k, j :: 0 <= k < i && 0 <= j < |b| ==> result[k][j] == a[k] * b[j]
  {
    var row := [];
    var j := 0;
    while j < |b|
      invariant 0 <= j <= |b|
      invariant |row| == j
      invariant forall k :: 0 <= k < j ==> row[k] == a[i] * b[k]
    {
      row := row + [a[i] * b[j]];
      j := j + 1;
    }
    result := result + [row];
    i := i + 1;
  }
}
// </vc-code>
