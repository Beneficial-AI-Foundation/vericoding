predicate sorted_seg(a:array<int>, i:int, j:int) //j excluded
requires 0 <= i <= j <= a.Length
reads a
{
  forall l, k :: i <= l <= k < j ==> a[l] <= a[k]
}

//IMPL 
method bubbleSort(a:array<int>, c:int, f:int)//f excluded
modifies a 
requires 0 <= c <= f <= a.Length //when c==f empty sequence
ensures sorted_seg(a,c,f) 
ensures multiset(a[c..f]) == old(multiset(a[c..f]))
ensures a[..c]==old(a[..c]) && a[f..]==old(a[f..])
{
    /* code modified by LLM (iteration 3): added ghost variable to track multiset invariant */
    ghost var original_multiset := multiset(a[c..f]);
    
    var i := c;
    while i < f
        invariant c <= i <= f
        invariant multiset(a[c..f]) == original_multiset
        invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
        invariant sorted_seg(a, c, i)
        invariant forall k, l :: c <= k < i && i <= l < f ==> a[k] <= a[l]
    {
        var j := f - 1;
        while j > i
            invariant i <= j < f
            /* code modified by LLM (iteration 3): fixed multiset invariant to be maintained in inner loop */
            invariant multiset(a[c..f]) == original_multiset
            invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
            invariant sorted_seg(a, c, i)
            invariant forall k, l :: c <= k < i && i <= l < f ==> a[k] <= a[l]
            invariant forall k :: j < k < f ==> a[j] <= a[k]
        {
            if a[j-1] > a[j] {
                /* code modified by LLM (iteration 3): removed problematic assertion and added proper multiset reasoning */
                assert j-1 >= i >= c && j < f;
                ghost var before_swap := multiset(a[c..f]);
                a[j-1], a[j] := a[j], a[j-1];
                /* code modified by LLM (iteration 3): assert multiset unchanged after swap with proper reasoning */
                assert multiset(a[c..f]) == before_swap == original_multiset;
            }
            j := j - 1;
        }
        i := i + 1;
    }
}