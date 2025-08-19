//ATOM
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
    if c >= f {
        return;
    }
    
    var end := f;
    while end > c
        /* code modified by LLM (iteration 1): outer loop reduces sorted boundary from right */
        invariant c <= end <= f
        invariant sorted_seg(a, end, f)
        invariant multiset(a[c..f]) == old(multiset(a[c..f]))
        invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
        invariant forall k, l :: c <= k < end && end <= l < f ==> a[k] <= a[l]
    {
        var j := c;
        while j < end - 1
            /* code modified by LLM (iteration 1): inner loop bubbles largest element to position end-1 */
            invariant c <= j < end
            invariant sorted_seg(a, end, f)
            invariant multiset(a[c..f]) == old(multiset(a[c..f]))
            invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
            invariant forall k, l :: c <= k < end && end <= l < f ==> a[k] <= a[l]
            invariant forall k :: c <= k <= j ==> forall l :: j < l < end ==> a[k] <= a[l]
        {
            if a[j] > a[j + 1] {
                /* code modified by LLM (iteration 1): swap adjacent elements if out of order */
                var temp := a[j];
                a[j] := a[j + 1];
                a[j + 1] := temp;
            }
            j := j + 1;
        }
        end := end - 1;
    }
}