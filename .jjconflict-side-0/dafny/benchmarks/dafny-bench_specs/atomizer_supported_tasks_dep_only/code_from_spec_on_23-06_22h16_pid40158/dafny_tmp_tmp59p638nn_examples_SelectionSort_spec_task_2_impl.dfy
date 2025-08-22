twostate predicate Preserved(a: array<int>, left: nat, right: nat)
    reads a
    requires left <= right <= a.Length
{
    multiset(a[left..right]) == multiset(old(a[left..right]))
}

//ATOM Ordered
predicate Ordered(a: array<int>, left: nat, right: nat)
    reads a
    requires left <= right <= a.Length
{
    forall i, j :: left <= i < j < right ==> a[i] <= a[j]
}

twostate predicate Sorted(a: array<int>)
    reads a
{
    Ordered(a,0,a.Length) && Preserved(a,0,a.Length)
}

//ATOM SelectionnSort
method FindMin(a: array<int>, start: nat) returns (minIndex: nat)
    requires start < a.Length
    ensures start <= minIndex < a.Length
    ensures forall k :: start <= k < a.Length ==> a[minIndex] <= a[k]
{
    minIndex := start;
    var i := start + 1;
    while i < a.Length
        invariant start <= minIndex < a.Length
        invariant start + 1 <= i <= a.Length
        invariant forall k :: start <= k < i ==> a[minIndex] <= a[k]
    {
        if a[i] < a[minIndex] {
            minIndex := i;
        }
        i := i + 1;
    }
}

/* code modified by LLM (iteration 1): helper lemma to prove multiset properties */
lemma SwapPreservesMultiset(a: array<int>, i: nat, j: nat, oldSeq: seq<int>)
    requires 0 <= i < a.Length && 0 <= j < a.Length
    requires oldSeq == a[..]
    reads a
    ensures a[i] == oldSeq[j] && a[j] == oldSeq[i] ==> multiset(a[..]) == multiset(oldSeq)
{
    // The swap operation preserves the multiset
}

//IMPL SelectionSort
method SelectionSort(a: array<int>)
    modifies a
    ensures Sorted(a)
{
    /* code modified by LLM (iteration 1): capture original array state */
    ghost var originalArray := a[..];
    
    var i := 0;
    while i < a.Length
        decreases a.Length - i
        invariant 0 <= i <= a.Length
        invariant Ordered(a, 0, i)
        invariant forall p, q :: 0 <= p < i <= q < a.Length ==> a[p] <= a[q]
        /* code modified by LLM (iteration 1): preserve multiset throughout the loop */
        invariant multiset(a[..]) == multiset(originalArray)
    {
        var minIndex := FindMin(a, i);
        
        /* code modified by LLM (iteration 1): establish key properties before swap */
        assert forall k :: i <= k < a.Length ==> a[minIndex] <= a[k];
        assert forall p :: 0 <= p < i ==> forall k :: i <= k < a.Length ==> a[p] <= a[k];
        
        /* code modified by LLM (iteration 1): capture state before swap for multiset preservation */
        ghost var preSwapArray := a[..];
        
        a[i], a[minIndex] := a[minIndex], a[i];
        
        /* code modified by LLM (iteration 1): prove multiset preservation after swap */
        assert multiset(a[..]) == multiset(preSwapArray);
        assert multiset(preSwapArray) == multiset(originalArray);
        assert multiset(a[..]) == multiset(originalArray);
        
        /* code modified by LLM (iteration 1): prove ordering properties are maintained */
        assert forall p :: 0 <= p < i ==> a[p] <= a[i];
        assert forall q :: i < q < a.Length ==> a[i] <= a[q];
        assert Ordered(a, 0, i + 1);
        
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 1): establish final postcondition */
    assert Ordered(a, 0, a.Length);
    assert multiset(a[..]) == multiset(originalArray);
    assert Preserved(a, 0, a.Length);
    assert Sorted(a);
}