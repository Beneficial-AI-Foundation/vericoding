// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Min(a: int, b: int): int { if a <= b then a else b }
// </vc-helpers>

// <vc-spec>
method MergeSortedLists(arr1: array<int>, arr2: array<int>) returns (result: array<int>)
    requires 
        forall i, j :: 0 <= i < j < arr1.Length ==> arr1[i] <= arr1[j]
    requires
        forall i, j :: 0 <= i < j < arr2.Length ==> arr2[i] <= arr2[j]
    ensures
        forall i, j :: 0 <= i < j < result.Length ==> result[i] <= result[j]
    ensures
        result.Length == arr1.Length + arr2.Length
// </vc-spec>
// <vc-code>
{
  result := new int[arr1.Length + arr2.Length];
  var i := 0;
  var j := 0;
  var k := 0;
  while k < result.Length
    invariant 0 <= i <= arr1.Length
    invariant 0 <= j <= arr2.Length
    invariant k == i + j
    invariant k <= result.Length
    invariant forall p, q :: 0 <= p < q < k ==> result[p] <= result[q]
    invariant k == 0 || forall t :: i <= t < arr1.Length ==> result[k-1] <= arr1[t]
    invariant k == 0 || forall t :: j <= t < arr2.Length ==> result[k-1] <= arr2[t]
  {
    if i < arr1.Length && (j >= arr2.Length || arr1[i] <= arr2[j]) {
      result[k] := arr1[i];
      i := i + 1;
    } else {
      result[k] := arr2[j];
      j := j + 1;
    }
    k := k + 1;
  }
}
// </vc-code>
