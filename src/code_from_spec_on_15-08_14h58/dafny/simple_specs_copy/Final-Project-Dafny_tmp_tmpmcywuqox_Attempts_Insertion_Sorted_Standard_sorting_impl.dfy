//ATOM
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
        
        /* code modified by LLM (iteration 2): Store original values for tracking shifts */
        ghost var originalArray := Array[..];
        
        while j >= 0 && Array[j] > key
            invariant -1 <= j < i
            /* code modified by LLM (iteration 2): Maintain sortedness of unshifted portion */
            invariant InsertionSorted(Array, 0, j + 1)
            /* code modified by LLM (iteration 2): Elements that were shifted are greater than key */
            invariant forall k :: j + 2 <= k <= i ==> Array[k] > key
            /* code modified by LLM (iteration 2): Track that shifted elements come from original array */
            invariant forall k :: j + 2 <= k <= i ==> Array[k] == originalArray[k-1]
            /* code modified by LLM (iteration 2): Preserve values in unaffected positions */
            invariant forall k :: 0 <= k <= j ==> Array[k] == originalArray[k]
            /* code modified by LLM (iteration 2): Preserve sortedness beyond insertion point */
            invariant forall k :: i + 1 <= k < Array.Length ==> Array[k] == originalArray[k]
        {
            Array[j + 1] := Array[j];
            j := j - 1;
        }
        
        Array[j + 1] := key;
        
        /* code modified by LLM (iteration 2): Assert key properties for verification */
        assert j + 1 <= i;
        assert forall k :: 0 <= k <= j ==> Array[k] <= key;
        assert forall k :: j + 2 <= k <= i ==> key <= Array[k];
        
        i := i + 1;
    }
}