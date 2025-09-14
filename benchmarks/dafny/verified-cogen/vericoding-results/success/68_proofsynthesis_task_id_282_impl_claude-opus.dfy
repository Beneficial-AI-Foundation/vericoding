// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ElementWiseSubtract(arr1: array<int>, arr2: array<int>) returns (result: array<int>)
    requires arr1.Length == arr2.Length
    requires forall i :: 0 <= i < arr1.Length ==> -2147483648 <= arr1[i] - arr2[i] <= 2147483647
    ensures result.Length == arr1.Length
    ensures forall i :: 0 <= i < result.Length ==> result[i] == arr1[i] - arr2[i]
// </vc-spec>
// <vc-code>
{
  result := new int[arr1.Length];
  var i := 0;
  while i < arr1.Length
    invariant 0 <= i <= arr1.Length
    invariant forall j :: 0 <= j < i ==> result[j] == arr1[j] - arr2[j]
  {
    result[i] := arr1[i] - arr2[i];
    i := i + 1;
  }
}
// </vc-code>
