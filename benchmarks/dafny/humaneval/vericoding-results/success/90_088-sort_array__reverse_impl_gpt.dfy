// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): utility to compute reverse index for sequences */
function RevIndex(n: int, k: int): int { n - 1 - k }

/* helper modified by LLM (iteration 4): arithmetic fact about reverse indices being within bounds */
lemma RevIndexWithin(n: int, k: int)
  requires 0 < n
  requires 0 <= k < n
  ensures 0 <= RevIndex(n, k) < n
{ }
// </vc-helpers>

// <vc-spec>
method reverse(s: seq<int>) returns (rev: seq<int>)

  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): build reversed sequence iteratively without comprehensions */
  rev := [];
  var i := |s|;
  while i > 0
    invariant 0 <= i <= |s|
    invariant |rev| == |s| - i
    invariant forall k :: 0 <= k < |rev| ==> rev[k] == s[|s| - 1 - k]
    decreases i
  {
    i := i - 1;
    rev := rev + [s[i]];
  }
}
// </vc-code>
