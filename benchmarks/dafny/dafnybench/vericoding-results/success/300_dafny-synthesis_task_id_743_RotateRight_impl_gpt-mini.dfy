

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
method RotateRight(l: seq<int>, n: int) returns (r: seq<int>)
    requires n >= 0
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[(i - n + |l|) % |l|]
// </vc-spec>
// <vc-code>
{
  if |l| == 0 {
    r := l;
    return;
  }
  var len := |l|;
  r := [];
  var i := 0;
  while i < len
    invariant 0 <= i <= len
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==> r[j] == l[(j - n + len) % len]
  {
    r := r + [l[(i - n + len) % len]];
    i := i + 1;
  }
}
// </vc-code>

