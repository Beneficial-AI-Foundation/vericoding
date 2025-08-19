predicate InsertionSorted(Array: array<int>, left: int, right: int) 
 requires 0 <= left <= right <= Array.Length    
 reads Array    
{      
 forall i,j :: left <= i < j < right ==> Array[i] <= Array[j]
}

//IMPL
method sorting(Array: array<int>)
 requires Array.Length > 1 
 ensures InsertionSorted(Array, 0, Array.Length) 
 modifies Array
{
    var i := 1;
    while i < Array.Length
        invariant 1 <= i <= Array.Length
        invariant InsertionSorted(Array, 0, i)
    {
        var key := Array[i];
        var j := i - 1;
        
        while j >= 0 && Array[j] > key
            invariant -1 <= j < i
            invariant forall k :: j < k < i ==> Array[k] > key
            /* code modified by LLM (iteration 2): Simplified invariant for sorted portion */
            invariant j >= 0 ==> InsertionSorted(Array, 0, j + 1)
            /* code modified by LLM (iteration 2): Track elements that were shifted right */
            invariant forall k :: j + 2 <= k <= i ==> Array[k] > key
            /* code modified by LLM (iteration 2): Elements beyond position i are unchanged */
            invariant forall k :: i + 1 <= k < Array.Length ==> Array[k] == old(Array[k])
        {
            Array[j + 1] := Array[j];
            j := j - 1;
        }
        
        Array[j + 1] := key;
        
        /* code modified by LLM (iteration 2): Helper assertions to establish sorting property step by step */
        assert j + 1 <= i;
        assert Array[j + 1] == key;
        
        /* code modified by LLM (iteration 2): Prove elements to the left are <= key */
        if j >= 0 {
            assert Array[j] <= key; // Loop condition ensures this
        }
        
        /* code modified by LLM (iteration 2): Prove elements to the right are >= key */
        assert forall k :: j + 2 <= k <= i ==> Array[k] >= key;
        
        /* code modified by LLM (iteration 2): Establish sorting by cases */
        assert forall k1, k2 :: 0 <= k1 < k2 <= j + 1 ==> Array[k1] <= Array[k2];
        assert forall k1, k2 :: j + 1 <= k1 < k2 <= i ==> Array[k1] <= Array[k2];
        assert forall k1, k2 :: 0 <= k1 <= j + 1 && j + 1 < k2 <= i ==> Array[k1] <= Array[k2];
        
        /* code modified by LLM (iteration 2): Final assertion with proper reasoning */
        assert InsertionSorted(Array, 0, i + 1);
        
        i := i + 1;
    }
}