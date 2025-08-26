method SmallestListLength(s: seq<seq<int>>) returns (v: int)
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> v <= |s[i]|
    ensures exists i :: 0 <= i < |s| && v == |s[i]|
// </vc-spec>
// <vc-code>
{
  v := |s[0]|;
  var j := 1;
  
  while j < |s|
    invariant 1 <= j <= |s|
    invariant exists i :: 0 <= i < j && v == |s[i]|
    invariant forall i :: 0 <= i < j ==> v <= |s[i]|
  {
    if |s[j]| < v {
      v := |s[j]|;
    }
    j := j + 1;
  }
}
// </vc-code>