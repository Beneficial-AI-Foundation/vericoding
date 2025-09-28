// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): recursive minimum of non-empty sequence */
function Minimum(s: seq<int>): int
  requires |s| > 0
  ensures Minimum(s) in s
  ensures forall x :: x in s ==> Minimum(s) <= x
  decreases |s|
{
  if |s| == 1 then s[0]
  else let m := Minimum(s[1..]) in if s[0] <= m then s[0] else m
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && s[i] == sorted[j]
  ensures forall x :: x in s ==> x in sorted
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && sorted[i] == s[j]
  ensures forall x :: x in sorted ==> x in s
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): selection-sort using Minimum and iterative removal */
  var remaining: seq<int> := s;
  var out: seq<int> := [];
  while |remaining| > 0
    invariant multiset(out) + multiset(remaining) == multiset(s)
    invariant |out| + |remaining| == |s|
    invariant forall x, y :: x in out && y in remaining ==> x <= y
    invariant forall k :: 0 <= k + 1 < |out| ==> out[k] <= out[k+1]
    decreases |remaining|
  {
    var m := Minimum(remaining);
    var i := 0;
    while i < |remaining| && remaining[i] != m
      invariant 0 <= i <= |remaining|
      invariant forall k :: 0 <= k < i ==> remaining[k] != m
      decreases |remaining| - i
    {
      i := i + 1;
    }
    out := out + [m];
    remaining := remaining[..i] + remaining[i+1..];
  }
  sorted := out;
}
// </vc-code>
