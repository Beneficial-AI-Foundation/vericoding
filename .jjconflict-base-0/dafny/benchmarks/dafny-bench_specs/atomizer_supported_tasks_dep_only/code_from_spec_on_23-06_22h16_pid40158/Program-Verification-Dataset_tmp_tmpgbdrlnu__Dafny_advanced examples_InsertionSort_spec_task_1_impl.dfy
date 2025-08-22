// ATOM 
predicate sorted (a:array<int>, start:int, end:int) // all "before" end are sorted      
requires a!=null       
requires 0<=start<=end<=a.Length       
reads a       
{           
  forall j,k:: start<=j<k<end ==> a[j]<=a[k]
}

//IMPL 
method InsertionSort (a:array<int>)
requires a!=null && a.Length>1 
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
        
        /* code modified by LLM (iteration 3): Fixed loop invariants to properly maintain sorted property */
        while j >= 0 && a[j] > key
            invariant -1 <= j < i
            invariant sorted(a, 0, j + 1)
            invariant forall k :: j + 2 <= k <= i ==> a[k] == old(a[k])
            invariant forall k :: j + 2 <= k <= i ==> a[k] >= key
            invariant forall k :: 0 <= k <= j ==> a[k] == old(a[k])
            invariant forall k :: i + 1 <= k < a.Length ==> a[k] == old(a[k])
        {
            a[j + 1] := a[j];
            j := j - 1;
        }
        
        a[j + 1] := key;
        
        /* code modified by LLM (iteration 3): Added assertions to prove sorted property after insertion */
        assert a[j + 1] == key;
        assert forall k :: 0 <= k <= j ==> a[k] <= key;
        assert forall k :: j + 2 <= k <= i ==> a[k] >= key;
        
        /* code modified by LLM (iteration 3): Prove complete sortedness of range [0, i+1] */
        assert forall m, n :: 0 <= m < n <= j ==> a[m] <= a[n];
        assert forall m, n :: j + 2 <= m < n <= i ==> a[m] <= a[n];
        assert forall m, n :: 0 <= m <= j && m < j + 1 ==> a[m] <= a[j + 1];
        assert forall m, n :: j + 1 < n && n <= i ==> a[j + 1] <= a[n];
        
        i := i + 1;
    }
}

//ATOM_PLACEHOLDER_Main