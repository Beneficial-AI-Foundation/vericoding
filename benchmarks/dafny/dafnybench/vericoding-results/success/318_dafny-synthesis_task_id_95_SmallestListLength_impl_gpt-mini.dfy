

// <vc-helpers>
// (no helpers needed)
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
  var i := 1;
  while i < |s|
    invariant 1 <= i <= |s|
    invariant forall j :: 0 <= j < i ==> v <= |s[j]|
    invariant exists j :: 0 <= j < i && v == |s[j]|
  {
    if |s[i]| < v {
      v := |s[i]|;
    }
    i := i + 1;
  }
  return v;
}
// </vc-code>

