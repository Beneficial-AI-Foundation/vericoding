predicate sorted (a:array<int>, start:int, end:int) // all "before" end are sorted   
/* code modified by LLM (iteration 2): Removed unnecessary null check */
requires 0<=start<=end<=a.Length    
reads a    
{      
 forall j,k:: start<=j<k<end ==> a[j]<=a[k]
}

//IMPL
method InsertionSort (a:array<int>)
requires a.Length>1 
ensures sorted(a, 0, a.Length) 
modifies a
{
    var i := 1;
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant sorted(a, 0, i)
    {
        var key := a[i];
        var j := i - 1;
        
        /* code modified by LLM (iteration 3): Fixed inner loop invariants to properly track array modifications */
        while j >= 0 && a[j] > key
            invariant -1 <= j < i
            invariant forall k :: j < k < i ==> a[k] > key
            invariant forall k :: i < k < a.Length ==> a[k] == old(a[k])
            invariant key == old(a[i])
            invariant sorted(a, 0, j+1)
            invariant forall k :: j+2 <= k <= i ==> a[k] == old(a[k-1])
            invariant forall k :: 0 <= k <= j ==> a[k] == old(a[k])
        {
            a[j + 1] := a[j];
            j := j - 1;
        }
        
        a[j + 1] := key;
        
        /* code modified by LLM (iteration 3): Added proper assertions to establish sorted property */
        // After placing key at position j+1, prove sortedness up to i+1
        assert forall k1, k2 :: 0 <= k1 < k2 <= j ==> a[k1] <= a[k2]; // sorted(a, 0, j+1)
        assert forall k :: 0 <= k <= j ==> a[k] <= key; // everything before key is <= key
        assert forall k :: j+2 <= k <= i ==> key <= a[k]; // everything after key is >= key
        assert sorted(a, 0, i+1);
        
        i := i + 1;
    }
}