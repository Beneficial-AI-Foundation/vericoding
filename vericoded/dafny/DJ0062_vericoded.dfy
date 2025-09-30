// <vc-preamble>
type NestedSeq = seq<seq<int>>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method AllSequenceEqualLength(s: NestedSeq) returns (r: bool)
    requires |s| > 0
    ensures r == (forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> |s[i]| == |s[j]|)
// </vc-spec>
// <vc-code>
{
  if |s| == 1 {
    return true;
  }
  
  var firstLen := |s[0]|;
  var i := 1;
  
  while i < |s|
    invariant 1 <= i <= |s|
    invariant forall k :: 0 <= k < i ==> |s[k]| == firstLen
  {
    if |s[i]| != firstLen {
      return false;
    }
    i := i + 1;
  }
  
  return true;
}
// </vc-code>
