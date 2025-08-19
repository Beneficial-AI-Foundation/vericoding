//ATOM

predicate isSorted(a:array<int>)
 reads a
{
 forall i:nat :: i < a.Length - 1 ==> a[i] <= a[i+1]
}

//IMPL 

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
        invariant forall i:nat :: i < lo ==> a[i] < K
        invariant forall i:nat :: hi <= i < a.Length ==> a[i] > K
        /* code modified by LLM (iteration 1): added key invariant to maintain equivalence between K existing in array and in current search range */
        invariant (exists i:nat :: i < a.Length && a[i] == K) <==> (exists i:nat :: lo <= i < hi && a[i] == K)
    {
        var mid := (lo + hi) / 2;
        
        /* code modified by LLM (iteration 1): added assertion to help with bounds checking */
        assert lo <= mid < hi;
        
        if a[mid] < K {
            /* code modified by LLM (iteration 1): added assertion to help prove invariant maintenance */
            assert forall i:nat :: i <= mid ==> a[i] < K;
            lo := mid + 1;
        } else if a[mid] > K {
            /* code modified by LLM (iteration 1): added assertion to help prove invariant maintenance */
            assert forall i:nat :: mid <= i < hi ==> a[i] > K;
            hi := mid;
        } else {
            /* code modified by LLM (iteration 1): when K is found, prove existence and return */
            assert a[mid] == K && mid < a.Length;
            b := true;
            return;
        }
    }
    
    /* code modified by LLM (iteration 1): when loop exits, search range is empty, so K cannot exist */
    assert lo == hi;
    assert forall i:nat :: lo <= i < hi ==> false;
    assert !(exists i:nat :: lo <= i < hi && a[i] == K);
    b := false;
}