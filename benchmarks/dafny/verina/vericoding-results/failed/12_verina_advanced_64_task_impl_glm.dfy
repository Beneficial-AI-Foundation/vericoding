// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed exists quantifier syntax */
function Contains(seq: seq<nat>, elem: nat): bool {
    (exists i :: 0 <= i < |seq| && seq[i] == elem)
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
/* code modified by LLM (iteration 5): fixed implementation to properly remove target elements */
{
    var newSeq := [];
    var i := 0;
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant forall j :: 0 <= j < |newSeq| ==> newSeq[j] != target
        invariant forall j :: 0 <= j < |newSeq| ==> exists k :: 0 <= k < |lst| && lst[k] == newSeq[j] && lst[k] != target
        invariant forall p, q :: 0 <= p < q < |newSeq| ==> (exists p_idx, q_idx :: 0 <= p_idx < q_idx < |lst| && lst[p_idx] == newSeq[p] && lst[q_idx] == newSeq[q])
    {
        if lst[i] != target {
            newSeq := newSeq + [lst[i]];
        }
        i := i + 1;
    }
    result := newSeq;
}
// </vc-code>
