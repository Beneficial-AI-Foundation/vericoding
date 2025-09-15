// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): simplified to use universal quantifier directly */
function allBelow(l: seq<int>, t: int): bool
    decreases |l|
{
    forall i : int :: i >= 0 && i < |l| ==> l[i] < t
}
// </vc-helpers>

// <vc-spec>
method below_threshold(l : seq<int>, t : int) returns (b : bool)

    ensures b == (forall i : int :: i >= 0 && i < |l| ==> l[i] < t)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): simplified to use the helper function */
  b := allBelow(l, t);
}
// </vc-code>
