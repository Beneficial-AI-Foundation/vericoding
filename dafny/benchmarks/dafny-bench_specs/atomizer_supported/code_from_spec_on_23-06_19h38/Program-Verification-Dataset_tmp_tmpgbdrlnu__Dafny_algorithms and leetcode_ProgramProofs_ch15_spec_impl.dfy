// ATOM 
predicate SplitPoint(a: array<int>, n: int)
    reads a
    requires 0 <= n <= a.Length
{
    forall i,j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
}

//IMPL SelectionSort
method SelectionSort(a: array<int>)
    modifies a
    ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures multiset(a[..]) == old(multiset(a[..]))
{
    /* code modified by LLM (iteration 1): Fixed for loop syntax and added proper invariants */
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall x,y :: 0 <= x < i <= y < a.Length ==> a[x] <= a[y]
        invariant forall x,y :: 0 <= x < y < i ==> a[x] <= a[y]
        invariant multiset(a[..]) == old(multiset(a[..]))
    {
        var minIndex := i;
        /* code modified by LLM (iteration 1): Fixed inner for loop syntax and invariants */
        var j := i + 1;
        while j < a.Length
            invariant i < j <= a.Length
            invariant i <= minIndex < a.Length
            invariant forall k :: i <= k < j ==> a[minIndex] <= a[k]
            invariant multiset(a[..]) == old(multiset(a[..]))
        {
            if a[j] < a[minIndex] {
                minIndex := j;
            }
            j := j + 1;
        }
        if minIndex != i {
            a[i], a[minIndex] := a[minIndex], a[i];
        }
        i := i + 1;
    }
}

//IMPL QuickSort
method QuickSort(a: array<int>)
    modifies a
    ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures multiset(a[..]) == old(multiset(a[..]))
{
    /* code modified by LLM (iteration 1): Added assertion to establish SplitPoint precondition */
    assert SplitPoint(a, 0) && SplitPoint(a, a.Length);
    QuickSortAux(a, 0, a.Length);
}

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
    /* code modified by LLM (iteration 1): Added decreases clause for termination */
    decreases hi - lo
{
    if lo + 1 < hi {
        var p := Partition(a, lo, hi);
        /* code modified by LLM (iteration 1): Added assertions to establish recursive call preconditions */
        assert SplitPoint(a, lo) && SplitPoint(a, p);
        QuickSortAux(a, lo, p);
        assert SplitPoint(a, p + 1) && SplitPoint(a, hi);
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
    
    /* code modified by LLM (iteration 1): Fixed for loop syntax and improved invariants */
    var j := lo;
    while j < hi - 1
        invariant lo <= i <= j <= hi - 1
        invariant forall k :: lo <= k < i ==> a[k] < pivot
        invariant forall k :: i <= k < j ==> a[k] >= pivot
        invariant a[hi - 1] == pivot
        invariant multiset(a[..]) == old(multiset(a[..]))
        invariant SplitPoint(a, lo) && SplitPoint(a, hi)
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
    
    /* code modified by LLM (iteration 1): Added assertions to verify postconditions */
    assert forall k :: lo <= k < p ==> a[k] < a[p];
    assert forall k :: p < k < hi ==> a[p] <= a[k];
    assert a[p] <= a[p];
}