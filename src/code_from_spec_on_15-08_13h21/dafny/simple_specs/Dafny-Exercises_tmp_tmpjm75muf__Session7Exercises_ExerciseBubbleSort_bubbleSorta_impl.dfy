//ATOM
predicate sorted_seg(a:array<int>, i:int, j:int) //j excluded
requires 0 <= i <= j <= a.Length
reads a
{
  forall l, k :: i <= l <= k < j ==> a[l] <= a[k]
}

//IMPL 
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
    
    var i := c;
    while i < f - 1
        invariant c <= i <= f - 1
        /* code modified by LLM (iteration 3): Maintain that [c..i] is sorted */
        invariant sorted_seg(a, c, i)
        /* code modified by LLM (iteration 3): Elements in sorted portion are <= all elements in unsorted portion */
        invariant forall k1, k2 :: c <= k1 < i && i <= k2 < f ==> a[k1] <= a[k2]
        invariant multiset(a[c..f]) == old(multiset(a[c..f]))
        invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
    {
        var j := i + 1;
        /* code modified by LLM (iteration 3): Find minimum in [i..f] and swap with a[i] */
        var min_idx := i;
        while j < f
            invariant i < j <= f
            invariant i <= min_idx < j
            /* code modified by LLM (iteration 3): min_idx points to minimum in [i..j) */
            invariant forall k :: i <= k < j ==> a[min_idx] <= a[k]
            invariant multiset(a[c..f]) == old(multiset(a[c..f]))
            invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
        {
            if a[j] < a[min_idx] {
                min_idx := j;
            }
            j := j + 1;
        }
        
        /* code modified by LLM (iteration 3): Swap minimum element to position i */
        if min_idx != i {
            a[i], a[min_idx] := a[min_idx], a[i];
        }
        
        i := i + 1;
    }
}