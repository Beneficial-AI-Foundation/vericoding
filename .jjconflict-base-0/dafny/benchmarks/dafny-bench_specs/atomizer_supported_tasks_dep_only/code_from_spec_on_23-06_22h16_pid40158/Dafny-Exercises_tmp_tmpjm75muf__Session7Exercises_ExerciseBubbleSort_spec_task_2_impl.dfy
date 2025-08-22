// ATOM 
predicate sorted_seg(a:array<int>, i:int, j:int) //j excluded
requires 0 <= i <= j <= a.Length
reads a
{
    forall l, k :: i <= l <= k < j ==> a[l] <= a[k]
}

//IMPL bubbleSort
method bubbleSort(a:array<int>, c:int, f:int)//f excluded
modifies a 
requires 0 <= c <= f <= a.Length //when c==f empty sequence
ensures sorted_seg(a,c,f) 
ensures multiset(a[c..f]) == old(multiset(a[c..f]))
ensures a[..c]==old(a[..c]) && a[f..]==old(a[f..])
{
    if c >= f {
        return;
    }
    
    /* code modified by LLM (iteration 3): Fixed bubble sort with corrected invariants */
    var i := f - 1;
    while i > c
        invariant c <= i < f
        invariant sorted_seg(a, i + 1, f)
        invariant multiset(a[c..f]) == old(multiset(a[c..f]))
        invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
        invariant forall k, l :: c <= k <= i && i + 1 <= l < f ==> a[k] <= a[l]
        decreases i - c
    {
        /* code modified by LLM (iteration 3): Store multiset before inner loop */
        ghost var ms_before := multiset(a[c..f]);
        
        var j := c;
        while j < i
            invariant c <= j <= i
            invariant sorted_seg(a, i + 1, f)
            invariant multiset(a[c..f]) == ms_before
            invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
            invariant forall k, l :: c <= k <= i && i + 1 <= l < f ==> a[k] <= a[l]
            invariant forall l :: j < l <= i ==> a[j] <= a[l]
            decreases i - j
        {
            if a[j] > a[j + 1] {
                /* code modified by LLM (iteration 3): Swap elements with multiset preservation */
                a[j], a[j + 1] := a[j + 1], a[j];
            }
            j := j + 1;
        }
        
        /* code modified by LLM (iteration 3): Assert properties after inner loop */
        assert forall l :: c <= l < i ==> a[l] <= a[i];
        assert multiset(a[c..f]) == ms_before;
        
        i := i - 1;
    }
    
    /* code modified by LLM (iteration 3): Final assertion for complete sortedness */
    assert i == c;
    assert forall k, l :: c <= k <= l < f ==> a[k] <= a[l];
    assert sorted_seg(a, c, f);
}