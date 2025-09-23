// <vc-preamble>
predicate sorted_seg(a:array<int>, i:int, j:int)
requires 0 <= i <= j <= a.Length
reads a
{
    forall l, k :: i <= l <= k < j ==> a[l] <= a[k]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method bubbleSort(a:array<int>, c:int, f:int)
modifies a 
requires 0 <= c <= f <= a.Length
ensures sorted_seg(a,c,f) 
ensures multiset(a[c..f]) == old(multiset(a[c..f]))
ensures a[..c]==old(a[..c]) && a[f..]==old(a[f..])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
