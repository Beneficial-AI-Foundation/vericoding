// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fix index out of range error by adding precondition i <= |l| in function below_threshold_helper and ensuring bound k < |l| in the ensures clause  */
function below_threshold_helper(l: seq<int>, t: int, i: int): bool
  requires i >= 0 && i <= |l|
  decreases |l| - i
  ensures below_threshold_helper(l, t, i) == (forall k :: k >= i && k < |l| ==> l[k] < t)
{
  if i >= |l| then true else l[i] < t && below_threshold_helper(l, t, i + 1)
}
// </vc-helpers>

// <vc-spec>
method below_threshold(l : seq<int>, t : int) returns (b : bool)

    ensures b == (forall i : int :: i >= 0 && i < |l| ==> l[i] < t)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Implement method by calling below_threshold_helper */
{
  b := below_threshold_helper(l, t, 0);
}
// </vc-code>
