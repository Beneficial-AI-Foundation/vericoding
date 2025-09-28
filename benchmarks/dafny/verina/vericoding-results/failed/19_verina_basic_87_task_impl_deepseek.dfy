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
/* helper modified by LLM (iteration 5): Fix helper function with proper preconditions and recursive case */
function FindMinIndexInRangeHelper(arr: array<int>, start: int, finish: int): (minIndex: int)
  requires 0 <= start <= finish <= arr.Length
  reads arr
  ensures start <= minIndex < finish
  ensures forall k :: start <= k < finish ==> arr[minIndex] <= arr[k]
  decreases finish - start
{
  if start == finish - 1 then
    start
  else
    var candidate := FindMinIndexInRangeHelper(arr, start + 1, finish);
    if arr[start] <= arr[candidate] then start else candidate
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
{
  /* code modified by LLM (iteration 5): Fixed loop invariants and array initialization */
  result := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> result[j] == a[j]
  {
    result[i] := a[i];
    i := i + 1;
  }
  
  var current := 0;
  while current < result.Length
    invariant 0 <= current <= result.Length
    invariant forall i, j :: 0 <= i <= j < current ==> result[i] <= result[j]
    invariant multiset(result[..]) == multiset(a[..])
  {
    var minIndex := FindMinIndexInRangeHelper(result, current, result.Length);
    Swap(result, current, minIndex);
    current := current + 1;
  }
}
// </vc-code>
