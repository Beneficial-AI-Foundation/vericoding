//ATOM
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
    
    var i := c;
    while i < f - 1
        invariant c <= i <= f - 1
        invariant sorted_seg(a, c, i + 1)
        invariant multiset(a[c..f]) == old(multiset(a[c..f]))
        invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
        /* code modified by LLM (iteration 1): strengthened invariant to maintain that sorted prefix elements are <= all unsorted suffix elements */
        invariant forall k, l :: c <= k <= i && i + 1 <= l < f ==> a[k] <= a[l]
    {
        var j := f - 1;
        
        while j > i
            invariant i < j < f
            invariant sorted_seg(a, c, i + 1)
            invariant multiset(a[c..f]) == old(multiset(a[c..f]))
            invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
            /* code modified by LLM (iteration 1): maintained invariant that sorted prefix elements are <= all unsorted suffix elements */
            invariant forall k, l :: c <= k <= i && i + 1 <= l < f ==> a[k] <= a[l]
            /* code modified by LLM (iteration 1): added invariant that a[j] is minimum in unsorted range [j..f) */
            invariant forall k :: j <= k < f ==> a[j] <= a[k]
        {
            if a[j-1] > a[j] {
                a[j-1], a[j] := a[j], a[j-1];
            }
            j := j - 1;
        }
        i := i + 1;
    }
}