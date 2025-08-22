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
        
        /* code modified by LLM (iteration 3): Track array state before inner operations */
        ghost var a_before_shift := a[..];
        
        while j >= 0 && a[j] > key
            invariant -1 <= j <= i-1
            /* code modified by LLM (iteration 3): Maintain sorted property for unshifted part */
            invariant j >= 0 ==> sorted_seg(a, 0, j)
            /* code modified by LLM (iteration 3): Maintain sorted property after shift */
            invariant j+2 <= i ==> sorted_seg(a, j+2, i)
            /* code modified by LLM (iteration 3): Elements after shift are greater than key */
            invariant forall k :: j+2 <= k <= i ==> key < a[k]
            /* code modified by LLM (iteration 3): Shifted elements relationship */
            invariant forall k :: j+2 <= k <= i ==> a[k] == a_before_shift[k-1]
            /* code modified by LLM (iteration 3): Unchanged prefix */
            invariant forall k :: 0 <= k <= j ==> a[k] == a_before_shift[k]
            /* code modified by LLM (iteration 3): Unchanged suffix */
            invariant forall k :: i+1 <= k < a.Length ==> a[k] == a_before_shift[k]
            /* code modified by LLM (iteration 3): Multiset preservation during shift */
            invariant multiset(a[..]) == multiset(a_before_shift)
            /* code modified by LLM (iteration 3): Key value preservation */
            invariant key == a_before_shift[i]
        {
            a[j+1] := a[j];
            j := j - 1;
        }
        
        a[j+1] := key;
        
        /* code modified by LLM (iteration 3): Assert sorted property after insertion */
        assert sorted_seg(a, 0, i);
        
        i := i + 1;
    }
}