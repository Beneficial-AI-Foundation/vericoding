//ATOM
predicate sorted (a:array<int>, start:int, end:int) // all "before" end are sorted   
requires 0<=start<=end<=a.Length    
reads a    
{      
  forall j,k:: start<=j<k<end ==> a[j]<=a[k]
}

//IMPL InsertionSort
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
        
        while j >= 0 && a[j] > key
            invariant -1 <= j < i
            /* code modified by LLM (iteration 1): added invariants to maintain sortedness */
            invariant sorted(a, 0, j + 1)
            invariant sorted(a, j + 2, i + 1)
            invariant forall k :: j + 2 <= k <= i ==> a[k] > key
            invariant forall k :: i + 1 < k < a.Length ==> a[k] == old(a[k])
            decreases j + 1
        {
            a[j + 1] := a[j];
            j := j - 1;
        }
        
        a[j + 1] := key;
        /* code modified by LLM (iteration 1): added assertion to help verification */
        assert sorted(a, 0, i + 1);
        i := i + 1;
    }
}