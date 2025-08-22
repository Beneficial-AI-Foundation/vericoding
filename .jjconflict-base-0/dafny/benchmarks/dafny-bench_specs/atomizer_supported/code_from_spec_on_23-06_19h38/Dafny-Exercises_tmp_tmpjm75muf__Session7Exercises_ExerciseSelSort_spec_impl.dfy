// ATOM 
predicate sorted_seg(a:array<int>, i:int, j:int) //j not included
requires 0 <= i <= j <= a.Length
reads a
{
    forall l, k :: i <= l <= k < j ==> a[l] <= a[k]
}

//IMPL selSort
method selSort (a:array<int>, c:int, f:int)//f excluded
modifies a 
requires 0 <= c <= f <= a.Length //when c==f empty sequence
ensures sorted_seg(a,c,f) 
ensures multiset(a[c..f]) == old(multiset(a[c..f]))
ensures a[..c]==old(a[..c]) && a[f..]==old(a[f..])
{
    var i := c;
    while i < f
        invariant c <= i <= f
        invariant sorted_seg(a, c, i)
        invariant forall x, y :: c <= x < i && i <= y < f ==> a[x] <= a[y]
        invariant multiset(a[c..f]) == old(multiset(a[c..f]))
        invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
    {
        var minIndex := i;
        var j := i + 1;
        
        while j < f
            invariant i <= minIndex < f
            invariant i <= j <= f
            invariant forall k :: i <= k < j ==> a[minIndex] <= a[k]
            invariant multiset(a[c..f]) == old(multiset(a[c..f]))
            invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
        {
            if a[j] < a[minIndex] {
                minIndex := j;
            }
            j := j + 1;
        }
        
        if minIndex != i {
            a[i], a[minIndex] := a[minIndex], a[i];
        }
        
        i := i + 1;
    }
}