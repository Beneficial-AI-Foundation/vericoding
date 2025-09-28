// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed compilation error by removing 'return' keyword in function body */
function SquareValue(x: int): int {
  x * x
}
// </vc-helpers>

// <vc-spec>
method Square(arr: array<int>) returns (result: array<int>)
    ensures
        result.Length == arr.Length &&
        forall i :: 0 <= i < arr.Length ==> result[i] == arr[i] * arr[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): created new array and iterated to fill it with squared values */
{
  result := new int[arr.Length];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall j :: 0 <= j < i ==> result[j] == arr[j] * arr[j]
  {
    result[i] := SquareValue(arr[i]);
    i := i + 1;
  }
}
// </vc-code>
