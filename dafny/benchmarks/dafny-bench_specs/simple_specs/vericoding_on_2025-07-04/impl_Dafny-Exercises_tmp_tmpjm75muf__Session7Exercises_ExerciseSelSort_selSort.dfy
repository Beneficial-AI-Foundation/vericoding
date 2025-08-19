//ATOM
predicate sorted_seg(a:array<int>, i:int, j:int) //j not included
requires 0 <= i <= j <= a.Length
reads a
{
  forall l, k :: i <= l <= k < j ==> a[l] <= a[k]
}

//IMPL
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
        invariant forall k, l :: c <= k < i && i <= l < f ==> a[k] <= a[l]
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
            var temp := a[i];
            a[i] := a[minIndex];
            a[minIndex] := temp;
        }
        
        i := i + 1;
    }
}