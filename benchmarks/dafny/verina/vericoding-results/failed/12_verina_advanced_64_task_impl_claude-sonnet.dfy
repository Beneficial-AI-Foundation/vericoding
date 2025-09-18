// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add lemma to help prove order preservation */
lemma OrderPreservationLemma(lst: seq<nat>, target: nat, result: seq<nat>, i: int, j: int)
    requires 0 <= i < j < |lst|
    requires lst[i] != target && lst[j] != target
    requires result == seq(k | 0 <= k < |lst| && lst[k] != target, k)
    ensures exists k1, k2 :: 0 <= k1 < k2 < |result| && lst[result[k1]] == lst[i] && lst[result[k2]] == lst[j]
{
    var count_before_i := |seq(k | 0 <= k < i && lst[k] != target, k)|;
    var count_before_j := |seq(k | 0 <= k < j && lst[k] != target, k)|;
    assert count_before_i < count_before_j;
}
// </vc-helpers>

// <vc-spec>
method RemoveElement(lst: seq<nat>, target: nat) returns (result: seq<nat>)
    ensures
        forall i :: 0 <= i < |result| ==> result[i] != target
    ensures
        forall i :: 0 <= i < |result| ==> 
            exists j :: 0 <= j < |lst| && lst[j] == result[i] && lst[j] != target
    ensures
        forall i, j :: 0 <= i < j < |lst| && lst[i] != target && lst[j] != target ==> 
            (exists k1, k2 :: 0 <= k1 < k2 < |result| && 
            result[k1] == lst[i] && result[k2] == lst[j])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed implementation with proper loop invariants */
    result := [];
    var i := 0;
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant forall k :: 0 <= k < |result| ==> result[k] != target
        invariant forall k :: 0 <= k < |result| ==> exists j :: 0 <= j < i && lst[j] == result[k] && lst[j] != target
        invariant forall x, y :: 0 <= x < y < i && lst[x] != target && lst[y] != target ==>
            (exists k1, k2 :: 0 <= k1 < k2 < |result| && result[k1] == lst[x] && result[k2] == lst[y])
    {
        if lst[i] != target {
            result := result + [lst[i]];
        }
        i := i + 1;
    }
}
// </vc-code>
