//ATOM
predicate sorted_seg(a:array<int>, i:int, j:int) //j excluded
requires 0 <= i <= j <= a.Length
reads a
{
  forall l, k :: i <= l <= k < j ==> a[l] <= a[k]
}

//IMPL bubbleSorta
method bubbleSorta(a:array<int>, c:int, f:int)//f excluded
modifies a 
requires 0 <= c <= f <= a.Length //when c==f empty sequence
ensures sorted_seg(a,c,f) 
ensures multiset(a[c..f]) == old(multiset(a[c..f]))
ensures a[..c]==old(a[..c]) && a[f..]==old(a[f..])
{
    if c >= f {
        return;
    }
    
    /* code modified by LLM (iteration 2): fixed outer loop bounds and invariants */
    var i := f - 1;
    while i > c
        invariant c <= i <= f - 1
        invariant sorted_seg(a, i + 1, f)
        invariant multiset(a[c..f]) == old(multiset(a[c..f]))
        invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
        invariant forall k, l :: i < k < f && c <= l <= i ==> a[l] <= a[k]
    {
        /* code modified by LLM (iteration 2): inner loop with corrected invariants */
        var j := c;
        while j < i
            invariant c <= j <= i
            invariant multiset(a[c..f]) == old(multiset(a[c..f]))
            invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
            invariant sorted_seg(a, i + 1, f)
            invariant forall k, l :: i < k < f && c <= l <= i ==> a[l] <= a[k]
            invariant forall k :: c <= k < j ==> a[k] <= a[j]
        {
            if a[j] > a[j + 1] {
                /* code modified by LLM (iteration 2): swap elements */
                var temp := a[j];
                a[j] := a[j + 1];
                a[j + 1] := temp;
            }
            j := j + 1;
        }
        /* code modified by LLM (iteration 2): after inner loop, maximum element is at position i */
        assert forall k :: c <= k < i ==> a[k] <= a[i];
        i := i - 1;
    }
    
    /* code modified by LLM (iteration 2): final assertion to establish sorted_seg(a, c, f) */
    assert sorted_seg(a, c + 1, f);
    assert forall k :: c < k < f ==> a[c] <= a[k];
}