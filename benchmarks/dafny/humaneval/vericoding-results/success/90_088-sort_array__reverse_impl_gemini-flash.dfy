// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma LengthOfAppend(s1: seq<int>, s2: seq<int>) ensures |s1 + s2| == |s1| + |s2| { }
// </vc-helpers>

// <vc-spec>
method reverse(s: seq<int>) returns (rev: seq<int>)

  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
// </vc-spec>
// <vc-code>
{
  rev := [];
  var i := |s| - 1;
  while i >= 0
    invariant 0 <= i + 1 <= |s|
    invariant |rev| == |s| - (i + 1)
    invariant forall k :: 0 <= k < |rev| ==> rev[k] == s[|s| - 1 - k]
  {
    rev := rev + [s[i]];
    i := i - 1;
  }
}
// </vc-code>
