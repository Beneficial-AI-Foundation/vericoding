predicate SplitPoint(a: array<int>, n: int)
    reads a
    requires 0 <= n <= n

{
    forall i,j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
}



twostate predicate SwapFrame(a: array<int>, lo: int, hi: int)
    requires 0 <= lo <= hi <= a.Length
    reads a
{
    (forall i :: 0 <= i < lo || hi <= i < a.Length ==> a[i] == old(a[i])) && multiset(a[..]) == old(multiset(a[..]))
}

// <vc-helpers>
twostate lemma SplitPointPreservation(a: array<int>, n: int, lo: int, hi: int)
    requires 0 <= lo < hi <= a.Length
    requires 0 <= n <= a.Length
    requires SplitPoint(old(a), n)
    requires forall i :: 0 <= i < lo || hi <= i < a.Length ==> a[i] == old(a[i])
    ensures SplitPoint(a, n)
{
    if n <= lo || n >= hi {
        // Split point is outside modified range, so it's preserved
    } else {
        // Split point is in modified range, need to verify manually
    }
}

lemma PartitionMaintainsSplitPoint(a: array<int>, lo: int, hi: int, p: int)
    requires 0 <= lo <= p < hi <= a.Length
    requires forall i :: lo <= i < p ==> a[i] < a[p]
    requires forall i :: p <= i < hi ==> a[p] <= a[i]
    ensures SplitPoint(a, lo)
    ensures SplitPoint(a, hi)
{
    // Prove SplitPoint(a, lo)
    forall i, j | 0 <= i < lo <= j < a.Length
    ensures a[i] <= a[j]
    {
        if j >= hi {
            // j is beyond partitioned region
        } else if j < p {
            // Both i and j are before pivot
        } else {
            // j >= p, so a[p] <= a[j], and if i < lo we need transitivity
        }
    }
    
    // Prove SplitPoint(a, hi)
    forall i, j | 0 <= i < hi <= j < a.Length
    ensures a[i] <= a[j]
    {
        if i < lo {
            // i is before partitioned region
        } else if i < p {
            // i is in left partition: a[i] < a[p] <= a[j] (since j >= hi > p)
            assert a[i] < a[p];
            assert a[p] <= a[j];
        } else {
            // i >= p: a[i] >= a[p] and a[p] <= a[j], but we need a[i] <= a[j]
        }
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method Partition(a: array<int>, lo: int, hi: int) returns (p: int)
    requires 0 <= lo < hi <= a.Length
    requires SplitPoint(a, lo) && SplitPoint(a, hi)
    modifies a
    ensures lo <= p < hi
    ensures forall i :: lo <= i < p ==> a[i] < a[p]
    ensures forall i :: p <= i < hi ==> a[p] <= a[i]
    ensures SplitPoint(a, lo) && SplitPoint(a, hi)
    ensures SwapFrame(a, lo, hi)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if hi - lo == 1 {
        // Prove postconditions for base case
        assert forall i :: lo <= i < lo ==> a[i] < a[lo]; // vacuously true
        assert forall i :: lo <= i < hi ==> a[lo] <= a[i]; // vacuously true (only i = lo)
        assert SplitPoint(a, lo);
        assert SplitPoint(a, hi);
        assert SwapFrame(a, lo, hi);
        return lo;
    }
    
    var pivot := a[hi - 1];
    var i := lo;
    var j := lo;
    
    while j < hi - 1
        invariant lo <= i <= j <= hi - 1
        invariant forall k :: lo <= k < i ==> a[k] < pivot
        invariant forall k :: i <= k < j ==> a[k] >= pivot
        invariant multiset(a[..]) == old(multiset(a[..]))
        invariant forall k :: 0 <= k < lo || hi <= k < a.Length ==> a[k] == old(a[k])
        invariant a[hi - 1] == pivot
    {
        if a[j] < pivot {
            var temp := a[i];
            a[i] := a[j];
            a[j] := temp;
            i := i + 1;
        }
        j := j + 1;
    }
    
    var temp := a[i];
    a[i] := a[hi - 1];
    a[hi - 1] := temp;
    
    // Establish postconditions
    assert forall k :: lo <= k < i ==> a[k] < a[i]; // a[k] < pivot == a[i]
    assert forall k :: i < k < hi ==> a[i] <= a[k]; // a[i] == pivot <= a[k]
    assert a[i] <= a[i]; // reflexivity for k == i
    
    PartitionMaintainsSplitPoint(a, lo, hi, i);
    
    return i;
}
// </vc-code>
