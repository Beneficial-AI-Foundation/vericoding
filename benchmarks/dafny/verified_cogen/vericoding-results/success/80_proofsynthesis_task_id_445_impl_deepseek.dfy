// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed array access by using requires clause bounds */
predicate ValidIndices(arr1: array<int>, arr2: array<int>)
  reads arr1, arr2
{
  arr1.Length == arr2.Length
}
predicate MultiplicationInBounds(arr1: array<int>, arr2: array<int>)
  reads arr1, arr2
  requires arr1.Length == arr2.Length
{
  forall i | 0 <= i < arr1.Length :: arr1[i] * arr2[i] >= -2147483648 && arr1[i] * arr2[i] <= 2147483647
}
function SafeMultiply(a: int, b: int): int
  ensures SafeMultiply(a, b) == a * b
{
  a * b
}
// </vc-helpers>

// <vc-spec>
method ElementWiseMultiplication(arr1: array<int>, arr2: array<int>) returns (result: array<int>)

    requires
        arr1.Length == arr2.Length
    requires
        forall i :: 0 <= i < arr1.Length ==> (arr1[i] * arr2[i] >= -2147483648 && arr1[i] * arr2[i] <= 2147483647)

    ensures
        result.Length == arr1.Length
    ensures
        forall i :: 0 <= i < result.Length ==> result[i] == arr1[i] * arr2[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed verification by using proper loop invariants */
{
  result := new int[arr1.Length];
  var index : int := 0;

  while index < arr1.Length
    invariant 0 <= index <= arr1.Length
    invariant result.Length == arr1.Length
    invariant forall j :: 0 <= j < index ==> result[j] == arr1[j] * arr2[j]
  {
    result[index] := SafeMultiply(arr1[index], arr2[index]);
    index := index + 1;
  }
}
// </vc-code>
