// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
predicate IsInRange(i: int, len: nat) { 0 <= i < len }
// </vc-helpers>

// <vc-spec>
method ElementWiseDivide(arr1: array<int>, arr2: array<int>) returns (result: array<int>)
    requires arr1.Length == arr2.Length
    requires forall i :: 0 <= i < arr2.Length ==> arr2[i] != 0
    requires forall i :: 0 <= i < arr1.Length ==> -2147483648 <= arr1[i] / arr2[i] <= 2147483647
    ensures result.Length == arr1.Length
    ensures forall i :: 0 <= i < result.Length ==> result[i] == arr1[i] / arr2[i]
// </vc-spec>
// <vc-code>
{
  var n := arr1.Length;
  result := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result.Length == n
    invariant forall k :: 0 <= k < i ==> result[k] == arr1[k] / arr2[k]
    decreases n - i
  {
    assert 0 <= i < arr2.Length;
    result[i] := arr1[i] / arr2[i];
    i := i + 1;
  }
}
// </vc-code>
