// ATOM 
predicate SplitPoint(a: array<int>, n: int)
    reads a
    requires 0 <= n <= a.Length
{
    forall i,j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
}

//ATOM_PLACEHOLDER_SelectionSort

//ATOM_PLACEHOLDER_QuickSort

twostate predicate SwapFrame(a: array<int>, lo: int, hi: int)
    requires 0 <= lo <= hi <= a.Length
    reads a
{
    (forall i :: 0 <= i < lo || hi <= i < a.Length ==> a[i] == old(a[i])) && multiset(a[..]) == old(multiset(a[..]))
}

//IMPL QuickSortAux
method QuickSortAux(a: array<int>, lo: int, hi: int)
    requires 0 <= lo <= hi <= a.Length
    requires SplitPoint(a, lo) && SplitPoint(a, hi)
    modifies a
    ensures forall i,j :: lo <= i < j < hi ==> a[i] <= a[j]
    ensures SwapFrame(a, lo, hi)
    ensures SplitPoint(a, lo) && SplitPoint(a, hi)
    decreases hi - lo
{
    if lo + 1 < hi {
        var p := Partition(a, lo, hi);
        QuickSortAux(a, lo, p);
        QuickSortAux(a, p + 1, hi);
    }
}

//IMPL Partition
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
    var pivot := a[hi - 1];
    var i := lo;
    var j := lo;
    
    while j < hi - 1
        invariant lo <= i <= j <= hi - 1
        invariant forall k :: lo <= k < i ==> a[k] < pivot
        invariant forall k :: i <= k < j ==> a[k] >= pivot
        invariant a[hi - 1] == pivot
        invariant SplitPoint(a, lo) && SplitPoint(a, hi)
        invariant multiset(a[..]) == old(multiset(a[..]))
        invariant forall k :: 0 <= k < lo || hi <= k < a.Length ==> a[k] == old(a[k])
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