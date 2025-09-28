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
/* helper modified by LLM (iteration 4): implement helper methods renamed to avoid duplicates */
method FindMinHelper(arr: array<int>, start: int, finish: int) returns (result: int)
  requires 
    start <= finish &&
    finish <= arr.Length &&
    start < arr.Length
  ensures
    start <= result < finish &&
    forall k :: start <= k < finish ==> arr[k] >= arr[result]
{
  result := start;
  var i := start + 1;
  while i < finish
    invariant start <= result < i < finish + 1
    invariant forall k :: start <= k < i ==> arr[k] >= arr[result]
  {
    if arr[i] < arr[result] {
      result := i;
    }
    i := i + 1;
  }
}

/* helper modified by LLM (iteration 4): implement Swap */
method SwapHelper(a: array<int>, i: int, j: int)
  requires
    0 <= i < a.Length &&
    0 <= j < a.Length
  modifies a
  ensures
    (a[i] == old(a[j]) && a[j] == old(a[i])) &&
    forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k])
{
  var temp := a[i];
  a[i] := a[j];
  a[j] := temp;
}
// </vc-helpers>

// <vc-spec>
method SelectionSort(a: array<int>) returns (result: array<int>)
    ensures
        result.Length == a.Length &&
        (forall i, j :: 0 <= i <= j < result.Length ==> result[i] <= result[j]) &&
        multiset(result[..]) == multiset(a[..])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): implement SelectionSort using renamed helper functions */
{
  result := new int[a.Length]((i) => a[i]);
  var idx := 0;
  while idx < result.Length
    invariant 0 <= idx <= result.Length
    invariant multiset(result[..]) == multiset(a[..])
    invariant forall p, q :: 0 <= p <= q < idx ==> result[p] <= result[q]
    invariant forall p :: 0 <= p < idx ==> forall q :: idx <= q < result.Length ==> result[p] <= result[q]
  {
    var minIdx := FindMinHelper(result, idx, result.Length);
    SwapHelper(result, idx, minIdx);
    idx := idx + 1;
  }
}
// </vc-code>
