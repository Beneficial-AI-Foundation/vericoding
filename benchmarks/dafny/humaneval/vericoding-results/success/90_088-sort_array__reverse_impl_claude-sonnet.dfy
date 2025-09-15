// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method reverse(s: seq<int>) returns (rev: seq<int>)

  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
// </vc-spec>
// <vc-code>
{
  rev := [];
  var i := |s|;
  while i > 0
    invariant 0 <= i <= |s|
    invariant |rev| == |s| - i
    invariant forall k :: 0 <= k < |rev| ==> rev[k] == s[|s| - 1 - k]
  {
    i := i - 1;
    rev := rev + [s[i]];
  }
}
// </vc-code>
