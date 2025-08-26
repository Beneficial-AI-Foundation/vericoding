// <vc-helpers>
// Helper predicate to check if a portion of an array is sorted
predicate sorted(a: array<int>, start: int, end: int)
  reads a
  requires 0 <= start <= end < a.Length
{
  forall i, j :: start <= i <= j <= end ==> a[i] <= a[j]
}

// Helper lemma to prove properties about swapping
lemma SwapPreservesOrder(a: array<int>, j: int, old_a: seq<int>)
  requires 0 <= j < a.Length - 1
  requires a.Length == |old_a|
  requires a[j] == old_a[j+1]
  requires a[j+1] == old_a[j]
  requires forall k :: 0 <= k < a.Length && k != j && k != j+1 ==> a[k] == old_a[k]
  ensures forall k :: j < k < a.Length ==> a[j] <= a[k] <==> (forall k :: j < k < a.Length && k != j+1 ==> old_a[j] <= old_a[k]) && old_a[j] <= old_a[j+1]
{
  // The postcondition needs to be proven step by step
  forall k | j < k < a.Length
    ensures a[j] <= a[k] <==> (forall k :: j < k < a.Length && k != j+1 ==> old_a[j] <= old_a[k]) && old_a[j] <= old_a[j+1]
  {
    if k == j + 1 {
      // a[j] = old_a[j+1], a[k] = a[j+1] = old_a[j]
      // So a[j] <= a[k] iff old_a[j+1] <= old_a[j]
    } else {
      // a[k] = old_a[k], a[j] = old_a[j+1]
      // So a[j] <= a[k] iff old_a[j+1] <= old_a[k]
    }
  }
}
// </vc-helpers>

// <vc-spec>
method BubbleSort(a: array?<int>)
  modifies a
  requires a != null
// </vc-spec>
// <vc-code>
{
  if a.Length <= 1 {
    return;
  }
  
  var n := a.Length;
  var i := 0;
  
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant i > 0 ==> sorted(a, n - i, n - 1)
    invariant forall k, k' :: 0 <= k <= n - 1 - i && n - i <= k' < n ==> a[k] <= a[k']
  {
    var j := 0;
    while j < n - 1 - i
      invariant 0 <= j <= n - 1 - i
      invariant i > 0 ==> sorted(a, n - i, n - 1)
      invariant forall k, k' :: 0 <= k <= n - 1 - i && n - i <= k' < n ==> a[k] <= a[k']
      invariant j > 0 ==> (forall k :: 0 <= k < j ==> a[k] <= a[j-1])
      invariant forall k :: j < k <= n - 1 - i ==> a[j] <= a[k]
    {
      if a[j] > a[j + 1] {
        var temp := a[j];
        a[j] := a[j + 1];
        a[j + 1] := temp;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>