// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
    invariant forall k :: 0 <= k < i ==> result[k] == arr[k] * arr[k]
  {
    result[i] := arr[i] * arr[i];
    i := i + 1;
  }
}
// </vc-code>
