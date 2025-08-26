// Let me implement bubble sort with the necessary loop invariants and helper lemmas:

predicate sorted_seg(a:array<int>, i:int, j:int) //j excluded
requires 0 <= i <= j <= a.Length
reads a
{
    forall l, k :: i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
lemma multiset_swap_preserves(a: array<int>, i: int, j: int, k: int, l: int)
  requires 0 <= i <= j <= a.Length
  requires 0 <= k < l < a.Length
  modifies a
  ensures multiset(a[i..j]) == old(multiset(a[i..j]))

lemma sorted_after_bubble(a: array<int>, c: int, i: int, f: int)
  requires 0 <= c <= i < f <= a.Length
  requires sorted_seg(a, i + 1, f)
  requires forall k :: c <= k <= i ==> a[k] <= a[i + 1]
  modifies {}
  ensures sorted_seg(a, i + 1, f)
// </vc-helpers>

// <vc-spec>
method bubbleSort(a:array<int>, c:int, f:int)//f excluded
modifies a 
requires 0 <= c <= f <= a.Length //when c==f empty sequence
ensures sorted_seg(a,c,f) 
ensures multiset(a[c..f]) == old(multiset(a[c..f]))
ensures a[..c]==old(a[..c]) && a[f..]==old(a[f..])
// </vc-spec>
// <vc-code>
{
  if c >= f { return; }
  
  var i := f - 1;
  while i > c
    invariant c <= i < f
    invariant sorted_seg(a, i + 1, f)
    invariant multiset(a[c..f]) == old(multiset(a[c..f]))
    invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
    invariant forall k :: c <= k <= i ==> (forall m :: i < m < f ==> a[k] <= a[m])
    decreases i - c
  {
    var j := c;
    ghost var old_multiset := multiset(a[c..f]);
    
    while j < i
      invariant c <= j <= i
      invariant sorted_seg(a, i + 1, f)
      invariant forall k :: i < k < f ==> a[j] <= a[k]
      invariant forall k :: c <= k < j ==> (forall m :: i < m < f ==> a[k] <= a[m])
      invariant multiset(a[c..f]) == old_multiset
      invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
      invariant forall k :: c <= k <= j ==> a[k] <= a[j]
      decreases i - j
    {
      if a[j] > a[j + 1] {
        a[j], a[j + 1] := a[j + 1], a[j];
      }
      j := j + 1;
    }
    
    assert forall k :: c <= k <= i ==> a[k] <= a[i + 1];
    i := i - 1;
  }
}
// </vc-code>