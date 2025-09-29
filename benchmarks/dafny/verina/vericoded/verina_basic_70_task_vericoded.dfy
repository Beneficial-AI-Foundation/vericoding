// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate ExistsInRange(a: seq<int>, p: int -> bool, start: nat, end: nat)
    requires end <= |a|
{
    exists i :: start <= i < end && p(a[i])
}

lemma ExistsInRangeSplit(a: seq<int>, p: int -> bool, start: nat, mid: nat, end: nat)
    requires start <= mid <= end <= |a|
    requires ExistsInRange(a, p, start, end)
    ensures ExistsInRange(a, p, start, mid) || ExistsInRange(a, p, mid, end)
{
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
        invariant forall k :: 0 <= k < result ==> !p(a[k])
        invariant exists i :: result <= i < |a| && p(a[i])
    {
        result := result + 1;
    }
}
// </vc-code>
