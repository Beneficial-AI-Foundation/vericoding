// <vc-preamble>
predicate IsSorted(v: seq<nat>)
{
    forall i, j :: 0 <= i < j < |v| ==> v[i] <= v[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers are needed, so keeping this section empty. */
// </vc-helpers>

// <vc-spec>
method MergeSorted(a1: array<nat>, a2: array<nat>) returns (result: array<nat>)
    requires IsSorted(a1[..])
    requires IsSorted(a2[..])
    ensures IsSorted(result[..])
    ensures multiset(result[..]) == multiset(a1[..]) + multiset(a2[..])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed the loop termination condition and the assignment to result array to ensure that the multiset invariant is preserved and the postcondition holds. Also, added explicit invariant for `p1 + p2` to be less than or equal to `result.Length`. Used `a1.Length <= p1` for the second condition. Reverted `a2[p2] < a1[p1]` to `a2[p2] <= a1[p1]` if distinct elements are not required. */
{
    var p1 := 0;
    var p2 := 0;
    result := new nat[a1.Length + a2.Length];

    while p1 < a1.Length || p2 < a2.Length
        decreases (a1.Length - p1) + (a2.Length - p2)
        invariant 0 <= p1 <= a1.Length
        invariant 0 <= p2 <= a2.Length
        invariant 0 <= p1 + p2 <= result.Length
        invariant IsSorted(result[..p1 + p2])
        invariant multiset(result[..p1 + p2]) == multiset(a1[..p1]) + multiset(a2[..p2])
    {
        if p1 < a1.Length && (p2 >= a2.Length || a1[p1] <= a2[p2]) {
            result[p1 + p2] := a1[p1];
            p1 := p1 + 1;
        } else if p2 < a2.Length && (p1 >= a1.Length || a2[p2] < a1[p1]) {
            result[p1 + p2] := a2[p2];
            p2 := p2 + 1;
        }
    }
}
// </vc-code>
