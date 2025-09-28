// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SquareOf(x: int): int {
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
{
  result := new int[arr.Length];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant result.Length == arr.Length
    invariant forall j :: 0 <= j < i ==> result[j] == arr[j] * arr[j]
    decreases arr.Length - i
  {
    result[i] := arr[i] * arr[i];
    i := i + 1;
  }
}
// </vc-code>
