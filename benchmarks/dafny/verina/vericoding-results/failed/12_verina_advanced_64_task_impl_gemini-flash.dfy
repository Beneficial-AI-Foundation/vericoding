// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added `(==)` to the type parameter `T` in `HasElement` to allow comparison. Fixed the `FilterOutTarget` loop invariant concerning the relative order of elements, by requiring the existence of `k1_res`, `k2_res` within the current `filtered` sequence, which ensures the property holds progressively. */
predicate HasElement<T(==)> (s: seq<T>, e: T)
{
    exists i :: 0 <= i < |s| && s[i] == e
}

method FilterOutTarget(lst: seq<nat>, target: nat) returns (filtered: seq<nat>)
    ensures (forall x :: x in filtered ==> x != target)
    ensures (forall x :: x in filtered ==> x in lst)
    ensures (forall x :: x in lst && x != target ==> HasElement(filtered, x))
    ensures (forall i, j :: 0 <= i < j < |lst| && lst[i] != target && lst[j] != target
        ==> (exists k1, k2 :: 0 <= k1 < k2 < |filtered| && filtered[k1] == lst[i] && filtered[k2] == lst[j]))
{
    filtered := [];
    var k := 0;
    while k < |lst|
        invariant 0 <= k <= |lst|
        invariant (forall x :: x in filtered ==> x != target)
        invariant (forall x :: x in filtered ==> x in lst)
        invariant (forall i_prime :: 0 <= i_prime < k && lst[i_prime] != target ==> HasElement(filtered, lst[i_prime]))
        invariant (forall i_prime, j_prime :: 0 <= i_prime < j_prime < k && lst[i_prime] != target && lst[j_prime] != target
            ==> (exists k1_res, k2_res :: 0 <= k1_res < k2_res < |filtered| && filtered[k1_res] == lst[i_prime] && filtered[k2_res] == lst[j_prime]))
    {
        if lst[k] != target {
            filtered := filtered + [lst[k]];
        }
        k := k + 1;
    }
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
/* code modified by LLM (iteration 5): No changes to the main method body; the previous fix still holds. The helper function `FilterOutTarget` correctly implements the logic and its ensures clauses are propagated to this method. */
{
    result := FilterOutTarget(lst, target);
}
// </vc-code>
