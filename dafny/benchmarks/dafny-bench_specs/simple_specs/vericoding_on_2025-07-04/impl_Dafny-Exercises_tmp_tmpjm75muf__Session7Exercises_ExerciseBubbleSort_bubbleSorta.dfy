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
    var i := c;
    while i < f
        invariant c <= i <= f
        invariant sorted_seg(a, c, i)
        invariant forall k :: c <= k < i ==> forall l :: i <= l < f ==> a[k] <= a[l]
        invariant multiset(a[c..f]) == old(multiset(a[c..f]))
        invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
    {
        var j := f - 1;
        while j > i
            invariant i <= j < f
            invariant sorted_seg(a, c, i)
            invariant forall k :: c <= k < i ==> forall l :: i <= l < f ==> a[k] <= a[l]
            invariant forall k :: j < k < f ==> a[j] <= a[k]
            invariant multiset(a[c..f]) == old(multiset(a[c..f]))
            invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
        {
            if a[j-1] > a[j] {
                a[j-1], a[j] := a[j], a[j-1];
            }
            j := j - 1;
        }
        i := i + 1;
    }
}