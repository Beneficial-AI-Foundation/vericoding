// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ContainsK(arr: array<int>, k: int) returns (result: bool)
    ensures result == (exists i :: 0 <= i < arr.Length && arr[i] == k)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed postcondition by adding loop invariants */
  var i: int := 0;
  result := false;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant result == exists j :: 0 <= j < i && arr[j] == k
  {
    if arr[i] == k {
      result := true;
      break;
    }
    i := i + 1;
  }
}
// </vc-code>
