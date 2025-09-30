predicate sorted_seg(a:array<int>, i:int, j:int) //j not included
requires 0 <= i <= j <= a.Length
reads a
{
    forall l, k :: i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
lemma sorted_seg_property(a: array<int>, i: int, j: int, k: int)
    requires 0 <= i <= j <= a.Length
    requires 0 <= i <= k < j
    requires sorted_seg(a, i, j)
    ensures a[i] <= a[k]
{
    assert i <= i <= k < j;
}
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
    while i < f
        invariant c <= i <= f
        invariant sorted_seg(a, c, i)
        invariant forall p, q :: c <= p < i <= q < f ==> a[p] <= a[q]
        invariant multiset(a[c..f]) == old(multiset(a[c..f]))
        invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
    {
        var minIdx := i;
        var j := i + 1;
        
        while j < f
            invariant i < j <= f
            invariant i <= minIdx < f
            invariant forall k :: i <= k < j ==> a[minIdx] <= a[k]
            invariant multiset(a[c..f]) == old(multiset(a[c..f]))
            invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
        {
            if a[j] < a[minIdx] {
                minIdx := j;
            }
            j := j + 1;
        }
        
        if minIdx != i {
            var temp := a[i];
            a[i] := a[minIdx];
            a[minIdx] := temp;
        }
        
        i := i + 1;
    }
}
// </vc-code>

