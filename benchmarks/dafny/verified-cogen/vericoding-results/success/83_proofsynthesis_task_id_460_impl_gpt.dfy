// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): retain simple minimum utility for potential use */
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method GetFirstElements(arr: array<array<int>>) returns (result: array<int>)

    requires
        forall i :: 0 <= i < arr.Length ==> arr[i].Length > 0

    ensures
        arr.Length == result.Length
    ensures
        forall i :: 0 <= i < arr.Length ==> result[i] == arr[i][0]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implement loop to fill result without null-check invariant to avoid warning */
  result := new int[arr.Length];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant result.Length == arr.Length
    invariant forall j :: 0 <= j < i ==> result[j] == arr[j][0]
    decreases arr.Length - i
  {
    result[i] := arr[i][0];
    i := i + 1;
  }
}
// </vc-code>
