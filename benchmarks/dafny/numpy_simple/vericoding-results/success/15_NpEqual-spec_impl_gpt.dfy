// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): kept simple equality helper */
function eq(a: int, b: int): bool { a == b }
// </vc-helpers>

// <vc-spec>
method Equal(a: array<int>, b: array<int>) returns (result: array<bool>)
    requires a.Length == b.Length
    ensures 
        result.Length == a.Length &&
        forall i :: 0 <= i < a.Length ==> result[i] == (a[i] == b[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implemented loop and removed null-comparison invariants to avoid warnings */
  var n := a.Length;
  result := new bool[n];
  var i := 0;
  while i < n
    invariant n == a.Length && n == b.Length
    invariant 0 <= i <= n
    invariant result.Length == n
    invariant forall j :: 0 <= j < i ==> result[j] == (a[j] == b[j])
    decreases n - i
  {
    result[i] := a[i] == b[i];
    i := i + 1;
  }
}
// </vc-code>
