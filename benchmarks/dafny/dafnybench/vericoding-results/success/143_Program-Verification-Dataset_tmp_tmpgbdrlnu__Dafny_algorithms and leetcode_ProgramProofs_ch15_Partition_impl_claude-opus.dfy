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
lemma SplitPointMaintained(a: array<int>, lo: int, hi: int, i: int, j: int)
    requires 0 <= lo < hi <= a.Length
    requires lo <= i < hi && lo <= j < hi
    requires SplitPoint(a, lo) && SplitPoint(a, hi)
    ensures a[i] <= a[j] || a[j] <= a[i]  // Any two elements in [lo, hi) are comparable
{
    // This is trivially true since <= is total on integers
}
// </vc-helpers>

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
// <vc-code>
{
    var pivot := a[hi - 1];
    var i := lo;
    var j := lo;
    
    while j < hi - 1
        invariant lo <= i <= j <= hi - 1
        invariant forall k :: lo <= k < i ==> a[k] < pivot
        invariant forall k :: i <= k < j ==> a[k] >= pivot
        invariant a[hi - 1] == pivot
        invariant SplitPoint(a, lo) && SplitPoint(a, hi)
        invariant SwapFrame(a, lo, hi)
    {
        if a[j] < pivot {
            a[i], a[j] := a[j], a[i];
            i := i + 1;
        }
        j := j + 1;
    }
    
    a[i], a[hi - 1] := a[hi - 1], a[i];
    p := i;
}
// </vc-code>

