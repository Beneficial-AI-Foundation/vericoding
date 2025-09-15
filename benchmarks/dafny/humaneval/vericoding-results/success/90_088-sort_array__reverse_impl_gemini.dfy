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
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |rev| == i
    invariant forall k :: 0 <= k < i ==> rev[k] == s[i - 1 - k]
  {
    rev := [s[i]] + rev;
    i := i + 1;
  }
}
// </vc-code>
