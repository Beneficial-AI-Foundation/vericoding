// ATOM 
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
    
    /* code modified by LLM (iteration 2): Reimplemented bubble sort with correct invariants */
    var i := f - 1;
    while i > c
        invariant c <= i < f
        invariant multiset(a[c..f]) == old(multiset(a[c..f]))
        invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
        invariant sorted_seg(a, i + 1, f)
        invariant forall k, l :: c <= k <= i && i < l < f ==> a[k] <= a[l]
        decreases i - c
    {
        var j := c;
        while j < i
            invariant c <= j <= i
            invariant multiset(a[c..f]) == old(multiset(a[c..f]))
            invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
            invariant sorted_seg(a, i + 1, f)
            invariant forall k, l :: c <= k <= i && i < l < f ==> a[k] <= a[l]
            invariant forall k :: c <= k < j ==> a[k] <= a[j]
            decreases i - j
        {
            if a[j] > a[j + 1] {
                a[j], a[j + 1] := a[j + 1], a[j];
            }
            j := j + 1;
        }
        i := i - 1;
    }
}