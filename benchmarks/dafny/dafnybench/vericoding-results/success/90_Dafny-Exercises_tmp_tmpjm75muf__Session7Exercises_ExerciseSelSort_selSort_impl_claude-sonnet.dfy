predicate sorted_seg(a:array<int>, i:int, j:int) //j not included
requires 0 <= i <= j <= a.Length
reads a
{
    forall l, k :: i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
lemma sorted_seg_extend(a: array<int>, i: int, j: int, k: int)
requires 0 <= i <= j <= k <= a.Length
requires sorted_seg(a, i, j)
requires sorted_seg(a, j, k)
requires j > i && k > j ==> a[j-1] <= a[j]
ensures sorted_seg(a, i, k)
{
}

lemma sorted_seg_single(a: array<int>, i: int)
requires 0 <= i < a.Length
ensures sorted_seg(a, i, i+1)
{
}

lemma multiset_swap_lemma(a: array<int>, i: int, j: int, c: int, f: int)
requires 0 <= c <= i < f <= a.Length
requires 0 <= c <= j < f <= a.Length
requires i != j
ensures multiset(a[c..f]) == old(multiset(a[c..f]))
{
}

lemma sorted_seg_preserve_after_swap(a: array<int>, c: int, i: int, minPos: int)
requires 0 <= c <= i < a.Length
requires 0 <= c <= minPos < a.Length
requires sorted_seg(a, c, i)
requires forall k :: i <= k < a.Length ==> a[minPos] <= a[k]
requires forall k :: c <= k < i ==> a[k] <= a[minPos]
ensures sorted_seg(a, c, i+1)
{
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
    invariant multiset(a[c..f]) == old(multiset(a[c..f]))
    invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
    invariant forall k1, k2 :: c <= k1 < i && i <= k2 < f ==> a[k1] <= a[k2]
  {
    var minPos := i;
    var j := i + 1;
    
    while j < f
      invariant i < j <= f
      invariant i <= minPos < f
      invariant forall k :: i <= k < j ==> a[minPos] <= a[k]
    {
      if a[j] < a[minPos] {
        minPos := j;
      }
      j := j + 1;
    }
    
    if minPos != i {
      var temp := a[i];
      a[i] := a[minPos];
      a[minPos] := temp;
    }
    
    assert forall k :: i+1 <= k < f ==> a[i] <= a[k];
    assert forall k1, k2 :: c <= k1 < i+1 && i+1 <= k2 < f ==> a[k1] <= a[k2];
    i := i + 1;
  }
}
// </vc-code>

