//ATOM

predicate isSorted(a:array<int>)
 reads a
{
 forall i:nat :: i < a.Length - 1 ==> a[i] <= a[i+1]
}

//IMPL 

// a[lo] <= a[lo+1] <= ... <= a[hi-2] <= a[hi-1] 
method binSearch(a:array<int>, K:int) returns (b:bool)
 requires isSorted(a)
 ensures b == exists i:nat :: i < a.Length && a[i] == K
{
    if a.Length == 0 {
        b := false;
        return;
    }
    
    var lo := 0;
    var hi := a.Length;
    
    while lo < hi 
        invariant 0 <= lo <= hi <= a.Length
        /* code modified by LLM (iteration 4): Fixed invariants - elements before lo are <= K (not strictly less) */
        invariant forall i:nat :: i < lo ==> a[i] < K
        /* code modified by LLM (iteration 4): Fixed invariants - elements at hi and after are >= K (not strictly greater) */
        invariant forall i:nat :: hi <= i < a.Length ==> a[i] > K
        /* code modified by LLM (iteration 4): Key correctness property - if K exists, it must be in the current search range */
        invariant (exists i:nat :: i < a.Length && a[i] == K) <==> (exists i:nat :: lo <= i < hi && a[i] == K)
    {
        var mid := lo + (hi - lo) / 2;
        
        if a[mid] < K {
            /* code modified by LLM (iteration 4): When a[mid] < K, we can safely eliminate everything up to and including mid */
            lo := mid + 1;
        } else if a[mid] > K {
            /* code modified by LLM (iteration 4): When a[mid] > K, we can safely eliminate mid and everything after */
            hi := mid;
        } else {
            /* code modified by LLM (iteration 4): Found exact match */
            b := true;
            return;
        }
    }
    
    /* code modified by LLM (iteration 4): When lo == hi, the search range is empty, so K doesn't exist */
    b := false;
}