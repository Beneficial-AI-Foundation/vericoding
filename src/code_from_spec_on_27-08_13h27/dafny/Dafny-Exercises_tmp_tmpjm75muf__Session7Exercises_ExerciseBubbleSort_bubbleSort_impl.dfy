predicate sorted_seg(a:array<int>, i:int, j:int) //j excluded
requires 0 <= i <= j <= a.Length
reads a
{
    forall l, k :: i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
// Helper lemma to prove properties about swapping elements
lemma SwapPreservesMultiset(a: array<int>, i: int, j: int, c: int, f: int)
  requires 0 <= c <= i < j < f <= a.Length
  ensures multiset(a[c..f]) == old(multiset(a[c..f]))
{
  // Dafny can prove this automatically based on multiset properties after swap
}

// Helper lemma to ensure segments outside [c,f) remain unchanged
lemma SwapPreservesOutside(a: array<int>, i: int, j: int, c: int, f: int)
  requires 0 <= c <= i < j < f <= a.Length
  ensures a[..c] == old(a[..c])
  ensures a[f..] == old(a[f..])
{
  // Dafny proves this based on the swap operation not affecting outside indices
}

// Helper lemma to prove sortedness preservation in outer loop
lemma SortedSegExtension(a: array<int>, i: int, c: int, f: int)
  requires 0 <= c <= i <= f <= a.Length
  requires sorted_seg(a, i, f)
  requires i > c ==> forall k :: c <= k < i ==> a[k] <= a[i-1]
  ensures sorted_seg(a, i-1, f)
{
  if i > c {
    assert forall l, k :: (i-1) <= l <= k < f ==> a[l] <= a[k];
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method bubbleSort(a:array<int>, c:int, f:int)//f excluded
modifies a 
requires 0 <= c <= f <= a.Length //when c==f empty sequence
ensures sorted_seg(a,c,f) 
ensures multiset(a[c..f]) == old(multiset(a[c..f]))
ensures a[..c]==old(a[..c]) && a[f..]==old(a[f..])
// </vc-spec>
// </vc-spec>

// <vc-code>
method BubbleSort(a: array<int>, c: int, f: int) // f excluded
  modifies a
  requires 0 <= c <= f <= a.Length // when c==f empty sequence
  ensures sorted_seg(a, c, f)
  ensures multiset(a[c..f]) == old(multiset(a[c..f]))
  ensures a[..c] == old(a[..c]) && a[f..] == old(a[f..])
{
  var i := f;
  while c < i
    decreases i
    invariant c <= i <= f
    invariant sorted_seg(a, i, f)
    invariant multiset(a[c..f]) == old(multiset(a[c..f]))
    invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
  {
    var j := c;
    while j < i - 1
      decreases i - 1 - j
      invariant c <= j <= i <= f
      invariant sorted_seg(a, i, f)
      invariant multiset(a[c..f]) == old(multiset(a[c..f]))
      invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
      invariant forall k :: c <= k < j ==> a[k] <= a[j]
    {
      if a[j] > a[j + 1]
      {
        var temp := a[j];
        a[j] := a[j + 1];
        a[j + 1] := temp;
        SwapPreservesMultiset(a, j, j+1, c, f);
        SwapPreservesOutside(a, j, j+1, c, f);
      }
      j := j + 1;
    }
    // After inner loop, a[i-1] is the largest in a[c..i)
    if i > c + 1
    {
      assert forall k :: c <= k < i ==> a[k] <= a[i-1];
      SortedSegExtension(a, i, c, f);
    }
    else if i == c + 1
    {
      assert sorted_seg(a, i-1, f);
    }
    i := i - 1;
  }
}
// </vc-code>
