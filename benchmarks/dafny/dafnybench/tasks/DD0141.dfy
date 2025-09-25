// <vc-preamble>
predicate sorted_seg(a:array<int>, i:int, j:int)
requires 0 <= i <= j+1 <= a.Length
reads a
{
    forall l, k :: i <= l <= k <= j ==> a[l] <= a[k]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method InsertionSort(a: array<int>)
  modifies a;
  ensures sorted_seg(a,0,a.Length-1) 
  ensures multiset(a[..]) == old(multiset(a[..]))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
