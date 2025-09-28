// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

    predicate existsAtIndex(a: seq<int>, p: int -> bool, i: int)
        requires 0 <= i < |a|
    {
        p(a[i])
    }

    predicate noEarlierMatch(a: seq<int>, p: int -> bool, result: nat)
        requires result <= |a|
    {
        forall k :: 0 <= k < result ==> !p(a[k])
    }

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
    
    while result < |a| && !p(a[result])
        invariant 0 <= result <= |a|
        invariant noEarlierMatch(a, p, result)
        invariant exists i :: result <= i < |a| && p(a[i])
    {
        result := result + 1;
    }
}
// </vc-code>
