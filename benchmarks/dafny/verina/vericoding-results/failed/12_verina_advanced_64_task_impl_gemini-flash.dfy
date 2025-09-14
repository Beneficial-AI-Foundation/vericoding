// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 5): Corrects loop invariant for the second postcondition by using `i` directly and simplifies the third invariant's logic by ensuring valid indices for the `exists` clause. */
{
    var newLst: seq<nat> := [];
    var i: nat := 0;
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant forall k :: 0 <= k < |newLst| ==> newLst[k] != target
        invariant forall k :: 0 <= k < |newLst| ==> (exists j :: (0 <= j < i) && lst[j] == newLst[k] && lst[j] != target)
        invariant forall u, v :: 0 <= u < v < i && lst[u] != target && lst[v] != target ==> (
            (exists k1, k2 :: 0 <= k1 < k2 < |newLst| && newLst[k1] == lst[u] && newLst[k2] == lst[v]) ||
            (forall k :: 0 <= k < |newLst| ==> newLst[k] != lst[u] || newLst[k] != lst[v]
            )
        )
    {
        if lst[i] != target {
            newLst := newLst + [lst[i]];
        }
        i := i + 1;
    }
    result := newLst;
}
// </vc-code>
