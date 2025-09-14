predicate sorted_seg(a:array<int>, i:int, j:int) //j not included
requires 0 <= i <= j <= a.Length
reads a
{
    forall l, k :: i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
// No additional helpers needed; the implementation can be verified directly with the given spec.
// </vc-helpers>

// <vc-spec>
method selSort (a:array<int>, c:int, f:int)//f excluded
modifies a 
requires 0 <= c <= f <= a.Length //when c==f empty sequence
ensures sorted_seg(a,c,f) 
ensures multiset(a[c..f]) == old(multiset(a[c..f]))
ensures a[..c]==old(a[..c]) && a[f..]==old(a[f..])
// </vc-spec>
// <vc-code>
{
    var i := c;
    while (i < f)
        invariant c <= i <= f
        invariant a[..c] == old(a[..c])
        invariant a[f..] == old(a[f..])
        invariant multiset(a[c..f]) == old(multiset(a[c..f]))
        invariant sorted_seg(a, c, i)
        invariant forall p, q :: c <= p < i && i <= q < f ==> a[p] <= a[q]
    {
        var minIndex := i;
        var j := i + 1;
        while (j < f)
            invariant i <= j <= f
            invariant i <= minIndex < j
            invariant forall k :: i <= k < j ==> a[minIndex] <= a[k]
        {
            if (a[j] < a[minIndex])
            {
                minIndex := j;
            }
            j := j + 1;
        }
        // Swap a[i] and a[minIndex]
        var temp := a[i];
        a[i] := a[minIndex];
        a[minIndex] := temp;
        i := i + 1;
    }
}
// </vc-code>

