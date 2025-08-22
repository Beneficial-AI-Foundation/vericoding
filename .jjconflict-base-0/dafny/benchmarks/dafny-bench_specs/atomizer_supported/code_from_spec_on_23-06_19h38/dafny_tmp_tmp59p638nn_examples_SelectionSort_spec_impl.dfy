twostate predicate Preserved(a: array<int>, left: nat, right: nat)
    reads a
    requires left <= right <= a.Length
{
    multiset(a[left..right]) == multiset(old(a[left..right]))
}

//ATOM 
ghost predicate Ordered(a: array<int>, left: nat, right: nat)
    reads a
    requires left <= right <= a.Length
{
    forall i: nat :: left < i < right ==> a[i-1] <= a[i]
}

twostate predicate Sorted(a: array<int>)
    reads a
{
    Ordered(a,0,a.Length) && Preserved(a,0,a.Length)
}

//IMPL SelectionnSort
method SelectionnSort(a: array<int>)
    modifies a
    ensures Sorted(a)
{
    if a.Length <= 1 {
        return;
    }
    
    var i := 0;
    while i < a.Length - 1
        invariant 0 <= i <= a.Length
        /* code modified by LLM (iteration 4): strengthened ordering invariant to handle i+1 bound */
        invariant Ordered(a, 0, i + 1)
        invariant forall j, k :: 0 <= j < i <= k < a.Length ==> a[j] <= a[k]
        invariant multiset(a[..]) == multiset(old(a[..]))
    {
        var minIndex := i;
        var j := i + 1;
        
        while j < a.Length
            invariant i < j <= a.Length
            invariant i <= minIndex < j
            invariant forall k :: i <= k < j ==> a[minIndex] <= a[k]
        {
            if a[j] < a[minIndex] {
                minIndex := j;
            }
            j := j + 1;
        }
        
        /* code modified by LLM (iteration 4): strengthened assertion for minimum element */
        assert forall k :: i <= k < a.Length ==> a[minIndex] <= a[k];
        
        if minIndex != i {
            /* code modified by LLM (iteration 4): added multiset preservation assertion */
            assert multiset(a[..]) == multiset(old(a[..]));
            a[i], a[minIndex] := a[minIndex], a[i];
            assert multiset(a[..]) == multiset(old(a[..]));
        }
        
        /* code modified by LLM (iteration 4): strengthened post-swap assertions */
        assert forall j, k :: 0 <= j < i + 1 <= k < a.Length ==> a[j] <= a[k];
        assert Ordered(a, 0, i + 1);
        
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 4): final assertion to establish postcondition */
    assert Ordered(a, 0, a.Length);
    assert multiset(a[..]) == multiset(old(a[..]));
}

//IMPL SelectionSort
method SelectionSort(a: array<int>)
    modifies a
    ensures Sorted(a)
{
    if a.Length <= 1 {
        return;
    }
    
    var i := 0;
    while i < a.Length - 1
        invariant 0 <= i <= a.Length
        /* code modified by LLM (iteration 4): strengthened ordering invariant to handle i+1 bound */
        invariant Ordered(a, 0, i + 1)
        invariant forall j, k :: 0 <= j < i <= k < a.Length ==> a[j] <= a[k]
        invariant multiset(a[..]) == multiset(old(a[..]))
    {
        var minIndex := i;
        var j := i + 1;
        
        while j < a.Length
            invariant i < j <= a.Length
            invariant i <= minIndex < j
            invariant forall k :: i <= k < j ==> a[minIndex] <= a[k]
        {
            if a[j] < a[minIndex] {
                minIndex := j;
            }
            j := j + 1;
        }
        
        /* code modified by LLM (iteration 4): strengthened assertion for minimum element */
        assert forall k :: i <= k < a.Length ==> a[minIndex] <= a[k];
        
        if minIndex != i {
            /* code modified by LLM (iteration 4): added multiset preservation assertion */
            assert multiset(a[..]) == multiset(old(a[..]));
            a[i], a[minIndex] := a[minIndex], a[i];
            assert multiset(a[..]) == multiset(old(a[..]));
        }
        
        /* code modified by LLM (iteration 4): strengthened post-swap assertions */
        assert forall j, k :: 0 <= j < i + 1 <= k < a.Length ==> a[j] <= a[k];
        assert Ordered(a, 0, i + 1);
        
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 4): final assertion to establish postcondition */
    assert Ordered(a, 0, a.Length);
    assert multiset(a[..]) == multiset(old(a[..]));
}