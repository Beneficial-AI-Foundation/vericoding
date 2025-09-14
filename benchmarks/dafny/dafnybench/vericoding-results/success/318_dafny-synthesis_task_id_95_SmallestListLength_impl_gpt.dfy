

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SmallestListLength(s: seq<seq<int>>) returns (v: int)
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> v <= |s[i]|
    ensures exists i :: 0 <= i < |s| && v == |s[i]|
// </vc-spec>
// <vc-code>
{
  v := |s[0]|;
  var j := 0;
  var idx := 1;
  while idx < |s|
    invariant 1 <= idx <= |s|
    invariant 0 <= j < idx
    invariant v == |s[j]|
    invariant forall k :: 0 <= k < idx ==> v <= |s[k]|
    decreases |s| - idx
  {
    if |s[idx]| < v {
      v := |s[idx]|;
      j := idx;
    }
    idx := idx + 1;
  }
  assert idx == |s|;
  assert 0 <= j < |s| && v == |s[j]|;
}
// </vc-code>

