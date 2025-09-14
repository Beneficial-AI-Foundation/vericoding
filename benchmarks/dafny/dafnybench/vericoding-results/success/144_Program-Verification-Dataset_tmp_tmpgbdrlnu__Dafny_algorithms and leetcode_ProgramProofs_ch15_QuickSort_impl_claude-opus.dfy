method Partition(a: array<int>, lo: int, hi: int) returns (p: int)
    requires 0 <= lo < hi <= a.Length
    modifies a
    ensures lo <= p < hi
{
  assume{:axiom} false;
}

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

method QuickSortAux(a: array<int>, lo: int, hi: int)
    requires 0 <= lo <= hi <= a.Length
    requires SplitPoint(a, lo) && SplitPoint(a, hi)
    modifies a
    ensures forall i,j :: lo <= i < j < hi ==> a[i] <= a[j]
    ensures SwapFrame(a, lo, hi)
    ensures SplitPoint(a, lo) && SplitPoint(a, hi)
    decreases hi - lo
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma SplitPointEmpty(a: array<int>)
    ensures SplitPoint(a, 0)
    ensures SplitPoint(a, a.Length)
{
    // SplitPoint(a, 0) holds vacuously since there are no i < 0
    // SplitPoint(a, a.Length) holds vacuously since there are no j >= a.Length
}
// </vc-helpers>

// <vc-spec>
method QuickSort(a: array<int>)
    modifies a
    ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures multiset(a[..]) == old(multiset(a[..]))
// </vc-spec>
// <vc-code>
{
    if a.Length > 0 {
        SplitPointEmpty(a);
        QuickSortAux(a, 0, a.Length);
    }
}
// </vc-code>

