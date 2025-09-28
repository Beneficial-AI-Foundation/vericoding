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
/* helper modified by LLM (iteration 5): Added helper to find minimum index in range */
method FindMinIndexHelper(arr: array<int>, start: int, finish: int) returns (minIdx: int)
  requires 0 <= start < finish <= arr.Length
  ensures start <= minIdx < finish
  ensures forall k :: start <= k < finish ==> arr[minIdx] <= arr[k]
{
  minIdx := start;
  var i := start + 1;
  while i < finish
    invariant start < i <= finish
    invariant start <= minIdx < i
    invariant forall k :: start <= k < i ==> arr[minIdx] <= arr[k]
  {
    if arr[i] < arr[minIdx] {
      minIdx := i;
    }
    i := i + 1;
  }
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
/* code modified by LLM (iteration 5): Fixed initial multiset invariant */
{
  result := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result.Length == a.Length
    invariant forall k :: 0 <= k < i ==> result[k] == a[k]
  {
    result[i] := a[i];
    i := i + 1;
  }
  
  if result.Length == 0 {
    return;
  }
  
  i := 0;
  while i < result.Length - 1
    invariant 0 <= i < result.Length
    invariant forall j, k :: 0 <= j <= k < i ==> result[j] <= result[k]
    invariant forall j :: 0 <= j < i ==> forall k :: i <= k < result.Length ==> result[j] <= result[k]
    invariant multiset(result[..]) == multiset(a[..])
  {
    var minIdx := FindMinIndexHelper(result, i, result.Length);
    if minIdx != i {
      var temp := result[i];
      result[i] := result[minIdx];
      result[minIdx] := temp;
    }
    i := i + 1;
  }
}
// </vc-code>
