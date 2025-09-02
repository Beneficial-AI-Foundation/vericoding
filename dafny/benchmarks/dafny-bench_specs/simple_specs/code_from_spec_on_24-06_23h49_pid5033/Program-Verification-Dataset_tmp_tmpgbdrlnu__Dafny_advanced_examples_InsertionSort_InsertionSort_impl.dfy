//ATOM
predicate sorted (a:array<int>, start:int, end:int) // all "before" end are sorted   
requires a!=null    
requires 0<=start<=end<=a.Length    
reads a    
{      
 forall j,k:: start<=j<k<end ==> a[j]<=a[k]
}

//IMPL InsertionSort
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
        var j := i;
        /* code modified by LLM (iteration 2): Simplified invariants to focus on essential properties for correctness */
        while j > 0 && a[j-1] > a[j]
            invariant 0 <= j <= i
            invariant forall k1, k2 :: 0 <= k1 < k2 < j ==> a[k1] <= a[k2]
            invariant forall k1, k2 :: j < k1 < k2 <= i ==> a[k1] <= a[k2]
            invariant j < i ==> (forall k :: j < k <= i ==> a[j] <= a[k])
        {
            a[j-1], a[j] := a[j], a[j-1];
            j := j - 1;
        }
        /* code modified by LLM (iteration 2): Added lemma call to establish sortedness after inner loop */
        assert j == 0 || a[j-1] <= a[j];
        assert forall k1, k2 :: 0 <= k1 < k2 <= i ==> a[k1] <= a[k2];
        i := i + 1;
    }
}