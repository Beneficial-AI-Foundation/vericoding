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

method Partition(a: array<int>, lo: int, hi: int) returns (p: int)
    requires 0 <= lo < hi <= a.Length
    requires SplitPoint(a, lo) && SplitPoint(a, hi)
    modifies a
    ensures lo <= p < hi
    ensures forall i :: lo <= i < p ==> a[i] < a[p]
    ensures forall i :: p <= i < hi ==> a[p] <= a[i]
    ensures SplitPoint(a, lo) && SplitPoint(a, hi)
    ensures SwapFrame(a, lo, hi)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma SwapPreservesSplitPoint(a: array<int>, lo: int, hi: int, i: int, j: int)
    requires 0 <= lo <= hi <= a.Length
    requires 0 <= i < a.Length && 0 <= j < a.Length
    requires SplitPoint(a, lo) && SplitPoint(a, hi)
    ensures SplitPoint(a, lo) && SplitPoint(a, hi)
{
}

twostate lemma SwapPreservesSwapFrame(a: array<int>, lo: int, hi: int, i: int, j: int)
    requires 0 <= lo <= hi <= a.Length
    requires 0 <= i < a.Length && 0 <= j < a.Length
    requires SwapFrame(a, lo, hi)
    ensures SwapFrame(a, lo, hi)
{
    assert forall k :: 0 <= k < lo || hi <= k < a.Length ==> a[k] == old(a[k]);
    assert multiset(a[..]) == old(multiset(a[..]));
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method QuickSortAux(a: array<int>, lo: int, hi: int)
    requires 0 <= lo <= hi <= a.Length
    requires SplitPoint(a, lo) && SplitPoint(a, hi)
    modifies a
    ensures forall i,j :: lo <= i < j < hi ==> a[i] <= a[j]
    ensures SwapFrame(a, lo, hi)
    ensures SplitPoint(a, lo) && SplitPoint(a, hi)
    decreases hi - lo
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if lo < hi - 1 {
        var p := Partition(a, lo, hi);
        assert SwapFrame(a, lo, hi);
        QuickSortAux(a, lo, p);
        assert SwapFrame(a, lo, hi);
        QuickSortAux(a, p + 1, hi);
        assert SwapFrame(a, lo, hi);
    }
}
// </vc-code>
