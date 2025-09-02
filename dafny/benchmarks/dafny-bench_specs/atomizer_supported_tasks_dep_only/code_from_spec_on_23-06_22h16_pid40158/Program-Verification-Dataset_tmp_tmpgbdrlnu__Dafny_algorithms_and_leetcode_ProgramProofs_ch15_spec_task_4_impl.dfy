// ATOM 
predicate SplitPoint(a: array<int>, n: int)
    reads a
    requires 0 <= n <= a.Length
{
    forall i,j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
}

//ATOM_PLACEHOLDER_SelectionSort
method SelectionSort(a: array<int>)
    modifies a
    ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures multiset(a[..]) == old(multiset(a[..]))
{
    // Placeholder implementation
    assume false;
}

//ATOM_PLACEHOLDER_QuickSort
method QuickSort(a: array<int>)
    modifies a
    ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures multiset(a[..]) == old(multiset(a[..]))
{
    // Placeholder implementation
    assume false;
}

twostate predicate SwapFrame(a: array<int>, lo: int, hi: int)
    requires 0 <= lo <= hi <= a.Length
    reads a
{
    (forall i :: 0 <= i < lo || hi <= i < a.Length ==> a[i] == old(a[i])) && multiset(a[..]) == old(multiset(a[..]))
}

//ATOM_PLACEHOLDER_QuickSortAux
method QuickSortAux(a: array<int>, lo: int, hi: int)
    requires 0 <= lo <= hi <= a.Length
    modifies a
    ensures forall i,j :: lo <= i < j < hi ==> a[i] <= a[j]
    ensures multiset(a[..]) == old(multiset(a[..]))
    ensures forall i :: 0 <= i < lo || hi <= i < a.Length ==> a[i] == old(a[i])
{
    // Placeholder implementation
    assume false;
}

// IMPL Partition
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
        invariant multiset(a[..]) == old(multiset(a[..]))
        invariant forall k :: 0 <= k < lo || hi <= k < a.Length ==> a[k] == old(a[k])
        /* code modified by LLM (iteration 1): Added invariants to preserve SplitPoint properties */
        invariant forall x,y :: 0 <= x < lo <= y < a.Length ==> a[x] <= a[y]
        invariant forall x,y :: 0 <= x < hi <= y < a.Length ==> a[x] <= a[y]
    {
        if a[j] < pivot {
            a[i], a[j] := a[j], a[i];
            i := i + 1;
        }
        j := j + 1;
    }
    
    a[i], a[hi - 1] := a[hi - 1], a[i];
    p := i;

    /* code modified by LLM (iteration 1): Added assertions to help verify postconditions */
    assert forall k :: lo <= k < p ==> a[k] < pivot;
    assert forall k :: p < k < hi ==> pivot <= a[k];
    assert a[p] == pivot;
}