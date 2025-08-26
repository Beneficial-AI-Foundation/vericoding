predicate sorted_seg(a:array<int>, i:int, j:int) //j not included
requires 0 <= i <= j <= a.Length
reads a
{
    forall l, k :: i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
method findMin(a: array<int>, start: int, end: int) returns (minIndex: int)
requires 0 <= start < end <= a.Length
ensures start <= minIndex < end
ensures forall k :: start <= k < end ==> a[minIndex] <= a[k]
{
    minIndex := start;
    var i := start + 1;
    while i < end
    invariant start <= minIndex < i <= end
    invariant forall k :: start <= k < i ==> a[minIndex] <= a[k]
    {
        if a[i] < a[minIndex] {
            minIndex := i;
        }
        i := i + 1;
    }
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
    if c >= f {
        return;
    }
    
    var i := c;
    while i < f - 1
    invariant c <= i <= f
    invariant sorted_seg(a, c, i)
    invariant forall p, q :: c <= p < i && i <= q < f ==> a[p] <= a[q]
    invariant multiset(a[c..f]) == old(multiset(a[c..f]))
    invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
    {
        var minIndex := findMin(a, i, f);
        
        // Swap elements at i and minIndex
        var temp := a[i];
        a[i] := a[minIndex];
        a[minIndex] := temp;
        
        i := i + 1;
    }
}
// </vc-code>