//ATOM
predicate isSorted(a:array<int>)
 reads a
{
 forall i:nat :: i < a.Length - 1 ==> a[i] <= a[i+1]
}

//IMPL binSearch
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
    
    /* code modified by LLM (iteration 3): simplified invariants to maintain basic binary search properties */
    while lo < hi
        invariant 0 <= lo <= hi <= a.Length
        invariant forall i:nat :: i < lo ==> a[i] < K
        invariant forall i:nat :: hi <= i < a.Length ==> a[i] > K
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
    
    /* code modified by LLM (iteration 3): simplified final reasoning using basic invariant properties */
    assert lo == hi;
    assert forall i:nat :: i < lo ==> a[i] < K;
    assert forall i:nat :: lo <= i < a.Length ==> a[i] > K;
    assert forall i:nat :: i < a.Length ==> a[i] != K;
    
    b := false;
}