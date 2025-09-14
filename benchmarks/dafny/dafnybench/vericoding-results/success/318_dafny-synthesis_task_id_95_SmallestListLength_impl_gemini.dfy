// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Replaced the let-expression with a call to a new `min` helper to fix a parsing error. */
function min(a: int, b: int): int { if a < b then a else b }

function min_len_rec(s: seq<seq<int>>, k: int): int
  requires |s| > 0
  requires 0 <= k < |s|
  ensures forall i :: k <= i < |s| ==> min_len_rec(s, k) <= |s[i]|
  ensures exists i :: k <= i < |s| && min_len_rec(s, k) == |s[i]|
  decreases |s| - k
{
  if k == |s| - 1 then
    |s[k]|
  else
    min(|s[k]|, min_len_rec(s, k + 1))
}
// </vc-helpers>

// <vc-spec>
method SmallestListLength(s: seq<seq<int>>) returns (v: int)
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> v <= |s[i]|
    ensures exists i :: 0 <= i < |s| && v == |s[i]|
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): No change needed as the fix was in the helper function. */
  v := min_len_rec(s, 0);
}
// </vc-code>
