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
  /* code modified by LLM (iteration 2): directly assign to out parameter and use while loop with invariants */
  result := new int[arr.Length];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant result.Length == arr.Length
    invariant forall j :: 0 <= j < i ==> result[j] == arr[j] * arr[j]
  {
    result[i] := arr[i] * arr[i];
    i := i + 1;
  }
}
// </vc-code>
