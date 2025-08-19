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
    var i := c;
    while i < f - 1
        invariant c <= i <= f
        /* code modified by LLM (iteration 4): Ensure bounds are valid before calling sorted_seg */
        invariant i + 1 <= f ==> sorted_seg(a, c, i + 1)
        invariant multiset(a[c..f]) == old(multiset(a[c..f]))
        invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
        /* code modified by LLM (iteration 4): Partition invariant - sorted prefix is <= unsorted suffix */
        invariant forall k, l :: c <= k <= i && i < l < f ==> a[k] <= a[l]
    {
        var j := f - 1;
        while j > i
            /* code modified by LLM (iteration 4): Fixed bounds */
            invariant i < j <= f - 1
            /* code modified by LLM (iteration 4): Maintain sorted property with proper bounds check */
            invariant i + 1 <= f ==> sorted_seg(a, c, i + 1)
            /* code modified by LLM (iteration 4): Elements after j are greater than or equal to a[j] */
            invariant forall k :: j < k < f ==> a[j] <= a[k]
            /* code modified by LLM (iteration 4): Maintain partition between sorted and processing parts */
            invariant forall k, l :: c <= k <= i && j <= l < f ==> a[k] <= a[l]
            invariant multiset(a[c..f]) == old(multiset(a[c..f]))
            invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
            /* code modified by LLM (iteration 4): Current minimum property - a[j] is min of a[i+1..j+1] */
            invariant forall k :: i < k <= j ==> a[j] <= a[k]
        {
            if a[j-1] > a[j] {
                a[j-1], a[j] := a[j], a[j-1];
            }
            j := j - 1;
        }
        i := i + 1;
    }
}