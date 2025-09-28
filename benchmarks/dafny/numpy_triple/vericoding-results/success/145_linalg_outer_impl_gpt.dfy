// <vc-preamble>
// Method to compute the outer product of two vectors
// Given vectors a and b, produces a matrix where result[i][j] = a[i] * b[j]
// </vc-preamble>

// <vc-helpers>
function mul(a: real, b: real): real { a * b }
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
  var res: seq<seq<real>> := [];
  var i: int := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |res| == i
    invariant forall k: int :: 0 <= k < i ==> |res[k]| == |b|
    invariant forall k: int, j0: int :: 0 <= k < i && 0 <= j0 < |b| ==> res[k][j0] == a[k] * b[j0]
    decreases |a| - i
  {
    var row: seq<real> := [];
    var j: int := 0;
    while j < |b|
      invariant 0 <= j <= |b|
      invariant |row| == j
      invariant forall t: int :: 0 <= t < j ==> row[t] == a[i] * b[t]
      decreases |b| - j
    {
      row := row + [a[i] * b[j]];
      j := j + 1;
    }
    res := res + [row];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
