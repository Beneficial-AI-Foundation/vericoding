//ATOM
predicate InsertionSorted(Array: array<int>, left: int, right: int) 
 requires 0 <= left <= right <= Array.Length    
 reads Array    
{      
 forall i,j :: left <= i < j < right ==> Array[i] <= Array[j]
}

//IMPL sorting
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
        
        /* code modified by LLM (iteration 4): Corrected invariants to properly track insertion sort state */
        while j >= 0 && Array[j] > key
            invariant -1 <= j < i
            invariant forall k :: j + 2 <= k <= i ==> Array[k] > key
            invariant InsertionSorted(Array, 0, j + 1)
            invariant forall k :: j + 2 <= k <= i ==> Array[k-1] <= Array[k]
        {
            Array[j + 1] := Array[j];
            j := j - 1;
        }
        
        Array[j + 1] := key;
        
        /* code modified by LLM (iteration 4): Added assertions to help prove sortedness after insertion */
        assert j + 1 <= i;
        assert Array[j + 1] == key;
        assert j >= -1 ==> (j == -1 || Array[j] <= key);
        assert forall k :: j + 2 <= k <= i ==> Array[k] >= key;
        assert InsertionSorted(Array, 0, j + 1);
        
        i := i + 1;
    }
}