// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): removed unused helper */
// </vc-helpers>

// <vc-spec>
method ContainsK(arr: array<int>, k: int) returns (result: bool)
    ensures result == (exists i :: 0 <= i < arr.Length && arr[i] == k)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): initialize result before loop */ {
  result := false;
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant result == (exists j :: 0 <= j < i && arr[j] == k)
  {
    if arr[i] == k {
      result := true;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
