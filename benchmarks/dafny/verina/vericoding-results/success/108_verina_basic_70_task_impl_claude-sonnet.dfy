// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed invalid lemma - lemmas cannot have loops or variable modifications */
// </vc-helpers>

// <vc-spec>
method LinearSearch3(a: seq<int>, p: int -> bool) returns (result: nat)
    requires 
        exists i :: 0 <= i < |a| && p(a[i])
    ensures 
        result < |a| &&
        p(a[result]) &&
        forall k :: 0 <= k < result ==> !p(a[k])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Direct implementation without helper lemma */
    result := 0;
    while result < |a| && !p(a[result])
        invariant 0 <= result <= |a|
        invariant forall k :: 0 <= k < result ==> !p(a[k])
        invariant result == |a| ==> exists i :: result <= i < |a| && p(a[i])
        decreases |a| - result
    {
        result := result + 1;
    }
}
// </vc-code>
