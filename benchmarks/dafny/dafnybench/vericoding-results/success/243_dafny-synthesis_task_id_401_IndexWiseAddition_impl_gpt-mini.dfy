

// <vc-helpers>
// (no helpers required)
// </vc-helpers>

// <vc-spec>
method IndexWiseAddition(a: seq<seq<int>>, b: seq<seq<int>>) returns (result: seq<seq<int>>)
    requires |a| > 0 && |b| > 0
    requires |a| == |b|
    requires forall i :: 0 <= i < |a| ==> |a[i]| == |b[i]|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == |a[i]|
    ensures forall i :: 0 <= i < |result| ==> forall j :: 0 <= j < |result[i]| ==> result[i][j] == a[i][j] + b[i][j]
// </vc-spec>
// <vc-code>
{
  var n := |a|;
  var out: seq<seq<int>> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |out| == i
    invariant forall k :: 0 <= k < |out| ==> |out[k]| == |a[k]|
    invariant forall k, j :: 0 <= k < |out| && 0 <= j < |out[k]| ==> out[k][j] == a[k][j] + b[k][j]
  {
    var m := |a[i]|;
    var row := new int[m];
    var j := 0;
    while j < m
      invariant 0 <= j <= m
      invariant forall kk :: 0 <= kk < j ==> row[kk] == a[i][kk] + b[i][kk]
    {
      row[j] := a[i][j] + b[i][j];
      j := j + 1;
    }
    out := out + [row[..]];
    i := i + 1;
  }
  result := out;
}
// </vc-code>

