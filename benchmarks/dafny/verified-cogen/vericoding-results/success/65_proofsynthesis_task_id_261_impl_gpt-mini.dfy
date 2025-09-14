// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added ValidDivision avoiding direct division and Div with precondition to prevent division by zero */
predicate ValidDivision(a: int, b: int) { b != 0 && (a == 0 || (a > 0 && b > 0) || (a < 0 && b < 0)) }
function Div(a: int, b: int): int
  requires b != 0
  ensures Div(a, b) == a / b
{ a / b }
// </vc-helpers>

// <vc-spec>
method ElementWiseDivision(arr1: array<int>, arr2: array<int>) returns (result: array<int>)
    requires arr1.Length == arr2.Length
    requires forall i :: 0 <= i < arr2.Length ==> arr2[i] != 0
    requires forall m :: 0 <= m < arr1.Length ==> arr1[m] / arr2[m] >= 0
    ensures result.Length == arr1.Length
    ensures forall i :: 0 <= i < result.Length ==> result[i] == arr1[i] / arr2[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Implement element-wise division using Div helper */
  result := new int[arr1.Length];
  var i := 0;
  while i < arr1.Length
    invariant 0 <= i <= arr1.Length
    invariant result.Length == arr1.Length
    invariant forall k :: 0 <= k < i ==> result[k] == arr1[k] / arr2[k]
    decreases arr1.Length - i
  {
    result[i] := Div(arr1[i], arr2[i]);
    i := i + 1;
  }
}
// </vc-code>
