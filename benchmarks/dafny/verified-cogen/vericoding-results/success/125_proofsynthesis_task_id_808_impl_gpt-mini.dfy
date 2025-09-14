// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): add reads clause and bound check */
predicate ExistsIn(arr: array<int>, k: int, n: int) reads arr { 0 <= n <= arr.Length && exists i :: 0 <= i < n && arr[i] == k }
// </vc-helpers>

// <vc-spec>
method ContainsK(arr: array<int>, k: int) returns (result: bool)
    ensures result == (exists i :: 0 <= i < arr.Length && arr[i] == k)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implement linear search with invariants */
  var i := 0;
  result := false;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant result == (exists j :: 0 <= j < i && arr[j] == k)
  {
    if arr[i] == k {
      result := true;
    }
    i := i + 1;
  }
}
// </vc-code>
