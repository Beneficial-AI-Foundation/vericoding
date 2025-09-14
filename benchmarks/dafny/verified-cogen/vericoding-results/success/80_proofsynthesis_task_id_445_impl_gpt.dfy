// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): simple multiplication helper used in loop body */
function Mul(a: int, b: int): int { a * b }
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
{
  /* code modified by LLM (iteration 2): removed always-true null invariant and used Mul helper */
  result := new int[arr1.Length];
  var i := 0;
  while i < arr1.Length
    invariant 0 <= i <= arr1.Length
    invariant result.Length == arr1.Length
    invariant forall k :: 0 <= k < i ==> result[k] == arr1[k] * arr2[k]
    decreases arr1.Length - i
  {
    result[i] := Mul(arr1[i], arr2[i]);
    i := i + 1;
  }
}
// </vc-code>
