// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Int32(x: int): bool { -2147483648 <= x && x <= 2147483647 }
/* helper modified by LLM (iteration 2): added precondition to Quot to avoid division-by-zero */
function Quot(a: int, b: int): int requires b != 0 { a / b }
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
  /* code modified by LLM (iteration 2): implemented element-wise division using loop with invariants */
  var n := arr1.Length;
  result := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result.Length == n
    invariant forall j :: 0 <= j < i ==> result[j] == arr1[j] / arr2[j]
  {
    result[i] := arr1[i] / arr2[i];
    i := i + 1;
  }
}
// </vc-code>
