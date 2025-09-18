// <vc-preamble>
method FindMinIndexInRange(arr: array<int>, start: int, finish: int) returns (result: int)
    requires 
        start <= finish &&
        finish <= arr.Length &&
        start < arr.Length
    ensures
        start <= result < finish
{
    // impl-start
    assume {:axiom} false;
    result := start;
    // impl-end
}

method Swap(a: array<int>, i: int, j: int)
    requires
        a.Length > 0 &&
        0 <= i < a.Length &&
        0 <= j < a.Length
    modifies a
    ensures
        a.Length == old(a.Length) &&
        (0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == old(a[j])) &&
        (0 <= i < a.Length && 0 <= j < a.Length ==> a[j] == old(a[i])) &&
        forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k])
{
    // impl-start
    assume {:axiom} false;
    // impl-end
}
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): No changes needed */

// </vc-helpers>

// <vc-spec>
method SelectionSort(a: array<int>) returns (result: array<int>)
    ensures
        result.Length == a.Length &&
        (forall i, j :: 0 <= i <= j < result.Length ==> result[i] <= result[j]) &&
        multiset(result[..]) == multiset(a[..])
// </vc-spec>
// <vc-code>

{
  /* code modified by LLM (iteration 5): Removed conditional branch for empty array to properly establish multiset equality invariant on loop entry */
  result := new int[a.Length];
  for k := 0 to a.Length - 1
    invariant 0 <= k <= a.Length
    invariant multiset(result[..k]) == multiset(a[..k])
  {
    result[k] := a[k];
  }
  for i := 0 to a.Length - 1
    invariant 0 <= i <= a.Length
    invariant multiset(result[..]) == multiset(a[..])
    invariant forall p, q :: 0 <= p <= q < i ==> result[p] <= result[q]
    invariant forall p :: i <= p < a.Length ==> forall q :: 0 <= q < i ==> result[q] <= result[p]
  {
    var minIdx := i;
    for j := i + 1 to a.Length
      invariant i <= minIdx < result.Length
      invariant forall m :: i <= m < j ==> result[minIdx] <= result[m]
    {
      if result[j] < result[minIdx] {
        minIdx := j;
      }
    }
    if minIdx != i {
      var temp := result[i];
      result[i] := result[minIdx];
      result[minIdx] := temp;
    }
  }
}

// </vc-code>
