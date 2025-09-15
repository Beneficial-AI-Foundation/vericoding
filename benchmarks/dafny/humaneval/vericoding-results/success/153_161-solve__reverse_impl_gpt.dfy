// <vc-preamble>
function is_alpha(c: char) : bool {
  'a' <= c <= 'z' || 'A' <= c <= 'Z'
}
function flip_case(c: char): (flipped: char)
  requires is_alpha(c)
  ensures is_alpha(flipped)
{
  if 'a' <= c <= 'z' then c - 'a' + 'A' else c - 'A' + 'a'
}
// </vc-preamble>

// <vc-helpers>
predicate IsReverseOf(s: string, rev: string) { |rev| == |s| && forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k] }
lemma SliceHeadIsIndex(s: string, i: int)
  requires 0 <= i < |s|
  ensures s[i..i+1][0] == s[i]
{ }
// </vc-helpers>

// <vc-spec>
method reverse(s: string) returns (rev: string)

  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
// </vc-spec>
// <vc-code>
{
  var n := |s|;
  var i := n;
  rev := "";
  while i > 0
    invariant 0 <= i <= n
    invariant |rev| == n - i
    invariant forall k :: 0 <= k < |rev| ==> rev[k] == s[n - 1 - k]
    decreases i
  {
    i := i - 1;
    rev := rev + s[i..i+1];
  }
}
// </vc-code>
