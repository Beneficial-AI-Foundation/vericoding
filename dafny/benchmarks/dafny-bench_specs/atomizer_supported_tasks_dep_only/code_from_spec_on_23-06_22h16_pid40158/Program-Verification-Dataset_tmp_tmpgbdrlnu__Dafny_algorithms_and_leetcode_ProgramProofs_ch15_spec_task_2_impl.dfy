// ATOM 
predicate SplitPoint(a: array<int>, n: int)
    reads a
    requires 0 <= n <= a.Length
{
    forall i,j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
}

//IMPL QuickSort
method QuickSort(a: array<int>)
    modifies a
    ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures multiset(a[..]) == old(multiset(a[..]))
{
    /* code modified by LLM (iteration 1): Added assertions to help prove the postconditions */
    QuickSortAux(a, 0, a.Length);
    assert SplitPoint(a, 0);
    assert SplitPoint(a, a.Length);
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
    decreases hi - lo
{
    if lo + 1 >= hi {
        return;
    }
    
    var p := Partition(a, lo, hi);
    /* code modified by LLM (iteration 1): Added assertions to help verify the recursive calls */
    assert SplitPoint(a, lo) && SplitPoint(a, hi);
    assert SplitPoint(a, p) && SplitPoint(a, p + 1);
    
    QuickSortAux(a, lo, p);
    QuickSortAux(a, p + 1, hi);
    
    /* code modified by LLM (iteration 1): Added assertions to help prove the final postcondition */
    assert forall i,j :: lo <= i < j < hi ==> 
        (i < p && j < p) || (i < p && j == p) || (i < p && j > p) || 
        (i == p && j > p) || (i > p && j > p);
}

/* code modified by LLM (iteration 1): Added helper lemma to establish SplitPoint preservation */
lemma SplitPointPreservation(a: array<int>, lo: int, hi: int, p: int)
    requires 0 <= lo <= p < hi <= a.Length
    requires SplitPoint(a, lo) && SplitPoint(a, hi)
    requires forall i :: lo <= i < p ==> a[i] < a[p]
    requires forall i :: p < i < hi ==> a[p] <= a[i]
    ensures SplitPoint(a, p) && SplitPoint(a, p + 1)
{
    // The lemma body is automatically proven by Dafny
}

//IMPL Partition
method Partition(a: array<int>, lo: int, hi: int) returns (p: int)
    requires 0 <= lo < hi <= a.Length
    requires SplitPoint(a, lo) && SplitPoint(a, hi)
    modifies a
    ensures lo <= p < hi
    ensures forall i :: lo <= i < p ==> a[i] < a[p]
    ensures forall i :: p < i < hi ==> a[p] <= a[i]
    ensures SplitPoint(a, lo) && SplitPoint(a, hi)
    ensures SwapFrame(a, lo, hi)
{
    var pivot := a[hi - 1];
    var i := lo;
    
    /* code modified by LLM (iteration 1): Added ghost variable to track original array state */
    ghost var original := a[..];
    
    for j := lo to hi - 1
        invariant lo <= i <= j
        invariant forall k :: lo <= k < i ==> a[k] < pivot
        invariant forall k :: i <= k < j ==> a[k] >= pivot
        invariant SplitPoint(a, lo) && SplitPoint(a, hi)
        invariant multiset(a[..]) == old(multiset(a[..]))
        invariant forall k :: 0 <= k < lo || hi <= k < a.Length ==> a[k] == old(a[k])
        /* code modified by LLM (iteration 1): Added invariant to track pivot position */
        invariant a[hi - 1] == pivot
    {
        if a[j] < pivot {
            /* code modified by LLM (iteration 1): Added assertions to help verify swap operation */
            assert a[hi - 1] == pivot;
            a[i], a[j] := a[j], a[i];
            assert a[hi - 1] == pivot;
            i := i + 1;
        }
    }
    
    /* code modified by LLM (iteration 1): Added assertions before final swap */
    assert a[hi - 1] == pivot;
    assert forall k :: lo <= k < i ==> a[k] < pivot;
    assert forall k :: i <= k < hi - 1 ==> a[k] >= pivot;
    
    a[i], a[hi - 1] := a[hi - 1], a[i];
    p := i;
    
    /* code modified by LLM (iteration 1): Added assertions to verify postconditions */
    assert a[p] == pivot;
    assert forall k :: lo <= k < p ==> a[k] < a[p];
    assert forall k :: p < k < hi ==> a[p] <= a[k];
    
    /* code modified by LLM (iteration 1): Call helper lemma to establish SplitPoint preservation */
    SplitPointPreservation(a, lo, hi, p);
}