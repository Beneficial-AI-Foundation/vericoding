// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
    result := 0;
    while result < |a|
        invariant 0 <= result <= |a|
        invariant forall k :: 0 <= k < result ==> !p(a[k])
        decreases |a| - result
    {
        if p(a[result]) {
            return;
        }
        result := result + 1;
    }
}
// </vc-code>
