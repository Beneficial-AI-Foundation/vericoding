// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Diff(a: int, b: int): int { a - b }

predicate InRangeSub(x: int, y: int) { -2147483648 <= x - y <= 2147483647 }

lemma SubBoundPreserved(arr1: array<int>, arr2: array<int>, i: int)
  requires arr1.Length == arr2.Length
  requires 0 <= i < arr1.Length
  requires forall j :: 0 <= j < arr1.Length ==> -2147483648 <= arr1[j] - arr2[j] <= 2147483647
  ensures -2147483648 <= arr1[i] - arr2[i] <= 2147483647
{ }
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
  var n := arr1.Length;
  result := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result.Length == n
    invariant forall k :: 0 <= k < i ==> result[k] == arr1[k] - arr2[k]
  {
    result[i] := arr1[i] - arr2[i];
    i := i + 1;
  }
}
// </vc-code>
