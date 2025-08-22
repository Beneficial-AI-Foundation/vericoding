// ATOM 
predicate sorted_seg(a:array<int>, i:int, j:int) //i and j included
requires 0 <= i <= j+1 <= a.Length
reads a
{
    forall l, k :: i <= l <= k <= j ==> a[l] <= a[k]
}

// IMPL 
method InsertionSort(a: array<int>)
  modifies a;
  ensures sorted_seg(a,0,a.Length-1) 
  ensures multiset(a[..]) == old(multiset(a[..])) //Add and prove this
{
    if a.Length <= 1 {
        return;
    }
    
    var i := 1;
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant sorted_seg(a, 0, i-1)
        invariant multiset(a[..]) == old(multiset(a[..]))
    {
        var key := a[i];
        var j := i - 1;
        
        /* code modified by LLM (iteration 3): Simplified inner loop with correct invariants */
        while j >= 0 && a[j] > key
            invariant -1 <= j <= i - 1
            invariant multiset(a[..]) == old(multiset(a[..]))
            /* code modified by LLM (iteration 3): Elements after j+1 up to i are shifted and > key */
            invariant forall k :: j+2 <= k <= i ==> a[k] > key
            /* code modified by LLM (iteration 3): Left part remains sorted */
            invariant j >= 0 ==> sorted_seg(a, 0, j)
            /* code modified by LLM (iteration 3): Right shifted part is sorted */
            invariant j+2 <= i ==> sorted_seg(a, j+2, i)
            /* code modified by LLM (iteration 3): Value at position i is preserved */
            invariant a[i] == key
        {
            a[j+1] := a[j];
            j := j - 1;
        }
        
        a[j+1] := key;
        
        /* code modified by LLM (iteration 3): Establish sortedness of the extended segment */
        if j >= 0 {
            assert sorted_seg(a, 0, j);
            assert a[j] <= key;
        }
        
        /* code modified by LLM (iteration 3): Key is in correct position relative to right part */
        assert forall k :: j+2 <= k <= i ==> key <= a[k];
        
        /* code modified by LLM (iteration 3): Prove the entire segment 0..i is sorted */
        assert forall l, m :: 0 <= l <= m <= i ==> 
            if l <= j && m == j+1 then a[l] <= key
            else if l == j+1 && m >= j+2 then key <= a[m]
            else if l <= j && m >= j+2 then a[l] <= a[m]
            else a[l] <= a[m];
        
        assert sorted_seg(a, 0, i);
        
        i := i + 1;
    }
}