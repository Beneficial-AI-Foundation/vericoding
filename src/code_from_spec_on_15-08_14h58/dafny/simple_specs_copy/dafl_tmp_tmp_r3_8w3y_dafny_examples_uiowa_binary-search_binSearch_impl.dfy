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
        /* code modified by LLM (iteration 4): weakened invariants to use <= and >= instead of strict inequalities */
        invariant forall i:nat :: i < lo ==> a[i] <= K
        invariant forall i:nat :: hi <= i < a.Length ==> a[i] >= K
        /* code modified by LLM (iteration 4): maintained invariant to ensure if K exists, it's in the remaining range */
        invariant (exists i:nat :: i < a.Length && a[i] == K) <==> (exists i:nat :: lo <= i < hi && a[i] == K)
    {
        var mid := (lo + hi) / 2;
        
        if a[mid] < K {
            lo := mid + 1;
        } else if a[mid] > K {
            hi := mid;
        } else {
            b := true;
            return;
        }
    }
    
    b := false;
}