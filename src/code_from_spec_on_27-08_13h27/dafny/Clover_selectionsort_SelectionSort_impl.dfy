// <vc-helpers>
// Helper lemma to prove that swapping elements preserves the multiset
lemma SwapPreservesMultiset(a: array<int>, i: int, j: int)
  requires 0 <= i < a.Length && 0 <= j < a.Length
  ensures multiset(a[..]) == multiset(a[..i] + [a[j]] + (if i+1 <= j then a[i+1..j] else []) + [a[i]] + (if j+1 < a.Length then a[j+1..] else []))
{
  // Dafny can prove this automatically
}

// Helper predicate to define that a prefix of the array is sorted
predicate IsSortedPrefix(a: array<int>, n: int)
  requires 0 <= n <= a.Length
  reads a
{
  forall i, j :: 0 <= i < j < n ==> a[i] <= a[j]
}

// Helper lemma to ensure that the minimum element in a range is correctly identified
lemma MinInRange(a: array<int>, start: int, end: int, minIdx: int)
  requires 0 <= start <= end <= a.Length
  requires start <= minIdx < end
  requires forall k :: start <= k < end ==> a[minIdx] <= a[k]
  ensures forall k :: start <= k < end ==> a[minIdx] <= a[k]
{
  // Dafny proves this automatically based on the loop invariants in the code
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method SelectionSort(a: array<int>)
  modifies a
  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == old(multiset(a[..]))
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  if a.Length <= 1 {
    return;
  }

  var i := 0;
  while i < a.Length - 1
    invariant 0 <= i < a.Length
    invariant IsSortedPrefix(a, i)
    invariant forall k, m :: 0 <= k < i <= m < a.Length ==> a[k] <= a[m]
    invariant multiset(a[..]) == old(multiset(a[..]))
  {
    var minIdx := i;
    var j := i + 1;
    while j < a.Length
      invariant i <= minIdx < a.Length
      invariant i < j <= a.Length
      invariant forall k :: i <= k < j ==> a[minIdx] <= a[k]
      invariant multiset(a[..]) == old(multiset(a[..]))
    {
      if a[j] < a[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }

    if minIdx != i {
      var temp := a[i];
      a[i] := a[minIdx];
      a[minIdx] := temp;
      // Use the lemma to prove multiset preservation after swap
      SwapPreservesMultiset(a, i, minIdx);
    }

    // Assert that after the swap, the element at i is the minimum in the range [i..a.Length)
    assert forall k :: i <= k < a.Length ==> a[i] <= a[k];
    i := i + 1;
  }
}
// </vc-code>
