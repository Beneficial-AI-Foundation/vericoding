method mergeSimple(a1: seq<int>, a2: seq<int>, start: int, end: int, b: array<int>)
  modifies b
  requires sorted_seq(a1)
  requires sorted_seq(a2)
  requires 0 <= start <= end <= b.Length
  requires |a1| +  |a2| == end - start + 1
  ensures sorted_slice(b, start, end)
// </vc-spec>
// <vc-code>
{
  var i1 := 0; // index for a1;
  var i2 := 0; // index for a2;
  var k := start; // index for b;
  
  while i1 < |a1| && i2 < |a2|
    invariant 0 <= i1 <= |a1|
    invariant 0 <= i2 <= |a2|
    invariant start <= k <= end
    invariant k == start + i1 + i2
    invariant k <= end
    invariant sorted_slice(b, start, k)
    invariant forall x :: start <= x < k ==> (i1 < |a1| ==> b[x] <= a1[i1])
    invariant forall x :: start <= x < k ==> (i2 < |a2| ==> b[x] <= a2[i2])
    invariant i1 + i2 + (|a1| - i1) + (|a2| - i2) == |a1| + |a2|
  {
    if a1[i1] <= a2[i2] {
      b[k] := a1[i1];
      i1 := i1 + 1;
    } else {
      b[k] := a2[i2];
      i2 := i2 + 1;
    }
    k := k + 1;
  }
  
  // Copy remaining elements from a1
  while i1 < |a1|
    invariant 0 <= i1 <= |a1|
    invariant i2 <= |a2|
    invariant start <= k <= end
    invariant k == start + i1 + i2
    invariant k <= end
    invariant sorted_slice(b, start, k)
    invariant forall x :: start <= x < k ==> (i1 < |a1| ==> b[x] <= a1[i1])
    invariant i2 == |a2|
  {
    b[k] := a1[i1];
    i1 := i1 + 1;
    k := k + 1;
  }
  
  // Copy remaining elements from a2
  while i2 < |a2|
    invariant i1 <= |a1|
    invariant 0 <= i2 <= |a2|
    invariant start <= k <= end
    invariant k == start + i1 + i2
    invariant k <= end
    invariant sorted_slice(b, start, k)
    invariant forall x :: start <= x < k ==> (i2 < |a2| ==> b[x] <= a2[i2])
    invariant i1 == |a1|
  {
    b[k] := a2[i2];
    i2 := i2 + 1;
    k := k + 1;
  }
  
  // At this point, k should equal end + 1
  assert k == start + |a1| + |a2|;
  assert k == start + (end - start + 1);
  assert k == end + 1;
  
  // We need to prove sorted_slice(b, start, end)
  // Since sorted_slice(b, start, k) and k == end + 1
  assert sorted_slice(b, start, k - 1);
  assert k - 1 == end;
  // Therefore sorted_slice(b, start, end) should hold
}
// </vc-code>

// <vc-helpers>
lemma sorted_slice_extension(a: array<int>, start: int, mid: int, end: int)
  requires 0 <= start <= mid <= end <= a.Length
  requires sorted_slice(a, start, mid)
  requires mid < end ==> (forall i :: start <= i < mid ==> a[i] <= a[mid])
  ensures sorted_slice(a, start, end) || !sorted_slice(a, mid, end)
{
  // Helper lemma for extending sorted slices
}

lemma sorted_slice_shrink(a: array<int>, start: int, k: int, end: int)
  requires 0 <= start <= end < k <= a.Length
  requires sorted_slice(a, start, k)
  ensures sorted_slice(a, start, end)
{
  // If a slice is sorted, any prefix is also sorted
}

lemma sorted_slice_inductive_step(a: array<int>, start: int, k: int)
  requires 0 <= start <= k < a.Length
  requires sorted_slice(a, start, k)
  requires k == start || a[k-1] <= a[k]
  ensures sorted_slice(a, start, k + 1)
{
  // Adding one element preserves sortedness if it's >= the last element
}
// </vc-helpers>

predicate merged(a1: seq<int>, a2: seq<int>, b: array<int>, start: int, end: int)
  reads b
  requires end - start  == |a2| + |a1|
  requires 0 <= start <= end <= b.Length
{
  multiset(a1) + multiset(a2) == multiset(b[start..end])
}

predicate sorted_slice(a: array<int>, start: int, end: int)
  requires 0 <= start <= end <= a.Length
  reads a
{
  forall i, j :: start <= i <= j < end ==> a[i] <= a[j]
}

predicate sorted_seq(a: seq<int>)
{
  forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
}

predicate sorted(a: array<int>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}