// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method IsSmaller(arr1: array<int>, arr2: array<int>) returns (result: bool)
    requires arr1.Length == arr2.Length
    ensures result == (forall i :: 0 <= i < arr1.Length ==> arr1[i] > arr2[i])
// </vc-spec>
// <vc-code>
{
  result := (forall i :: 0 <= i < arr1.Length ==> arr1[i] > arr2[i]);
}
// </vc-code>
