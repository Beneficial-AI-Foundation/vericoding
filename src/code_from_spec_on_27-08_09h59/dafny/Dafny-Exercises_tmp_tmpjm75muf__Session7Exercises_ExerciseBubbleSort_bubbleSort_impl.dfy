predicate sorted_seg(a:array<int>, i:int, j:int) //j excluded
requires 0 <= i <= j <= a.Length
reads a
{
    forall l, k :: i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
lemma sorted_seg_transitive(a: array<int>, i: int, j: int, k: int)
  requires 0 <= i <= j <= k <= a.Length
  requires sorted_seg(a, i, j)
  requires sorted_seg(a, j, k)
  requires j > i && k > j ==> a[j-1] <= a[j]
  ensures sorted_seg(a, i, k)
{
}

lemma sorted_seg_extend(a: array<int>, i: int, j: int)
  requires 0 <= i < j <= a.Length
  requires sorted_seg(a, i, j-1)
  requires j-1 > i ==> a[j-2] <= a[j-1]
  ensures sorted_seg(a, i, j)
{
}

lemma swap_preserves_multiset(a: array<int>, i: int, j: int, c: int, f: int)
  requires 0 <= c <= i < j < f <= a.Length
  requires a.Length > 0
{
  assert multiset(a[c..f]) == multiset(a[c..f]);
}

lemma bubble_step_sorts(a: array<int>, pos: int, start: int, end: int)
  requires 0 <= start <= pos < end - 1 <= a.Length
  requires forall k :: start <= k < pos ==> a[k] <= a[k+1]
  requires pos + 1 < a.Length
  requires a[pos] <= a[pos+1]
  ensures forall k :: start <= k < pos+1 ==> a[k] <= a[k+1]
{
}

lemma after_inner_loop_largest_at_end(a: array<int>, c: int, i: int)
  requires 0 <= c <= i < a.Length
  requires forall k :: c <= k < i ==> a[k] <= a[k+1]
  ensures forall k :: c <= k <= i ==> a[k] <= a[i]
{
  if c == i {
    return;
  }
  forall k | c <= k <= i
  ensures a[k] <= a[i]
  {
    if k == i {
      assert a[k] <= a[i];
    } else {
      var m := k;
      while m < i
        invariant k <= m <= i
        invariant a[k] <= a[m]
      {
        assert m < i;
        assert a[m] <= a[m+1];
        m := m + 1;
      }
    }
  }
}

lemma bubble_maintains_sorted_suffix(a: array<int>, c: int, i: int, f: int, j: int, old_a: seq<int>)
  requires 0 <= c <= j < i < f <= a.Length
  requires sorted_seg(a, i+1, f)
  requires forall k, l :: i < k <= l < f ==> a[k] <= a[l]
  requires a[..c] == old_a[..c] && a[f..] == old_a[f..]
  ensures sorted_seg(a, i+1, f)
  ensures forall k, l :: i < k <= l < f ==> a[k] <= a[l]
{
}

lemma multiset_after_swap(a: array<int>, c: int, f: int, j: int, old_multiset: multiset<int>)
  requires 0 <= c <= j < f <= a.Length
  requires j + 1 < f
  requires multiset(a[c..f]) == old_multiset
  ensures multiset(a[c..f]) == old_multiset
{
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
{
  if c >= f {
    return;
  }
  
  var i := f - 1;
  while i > c
    invariant c <= i < f
    invariant sorted_seg(a, i+1, f)
    invariant multiset(a[c..f]) == old(multiset(a[c..f]))
    invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
    invariant forall k :: i < k < f - 1 ==> a[k] <= a[k+1]
    invariant forall k, l :: i < k <= l < f ==> a[k] <= a[l]
    decreases i - c
  {
    var j := c;
    var loop_multiset := multiset(a[c..f]);
    while j < i
      invariant c <= j <= i
      invariant sorted_seg(a, i+1, f)
      invariant multiset(a[c..f]) == loop_multiset
      invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
      invariant forall k :: c <= k < j ==> a[k] <= a[k+1]
      invariant forall k :: c <= k <= j && j < i ==> a[k] <= a[j+1]
      invariant forall k, l :: i < k <= l < f ==> a[k] <= a[l]
      decreases i - j
    {
      if j + 1 < a.Length && a[j] > a[j+1] {
        var temp := a[j];
        a[j] := a[j+1];
        a[j+1] := temp;
      }
      j := j + 1;
    }
    if i < a.Length {
      after_inner_loop_largest_at_end(a, c, i);
    }
    i := i - 1;
  }
}
// </vc-code>
