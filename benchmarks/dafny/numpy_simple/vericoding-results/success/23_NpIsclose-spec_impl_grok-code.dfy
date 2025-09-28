// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method NpIsclose(a: array<int>, b: array<int>, tol: int) returns (result: array<bool>)
    requires 
        a.Length > 0 &&
        a.Length == b.Length &&
        tol > 0
    ensures
        result.Length == a.Length &&
        forall i :: 0 <= i < a.Length ==> 
            result[i] == (-tol < a[i] - b[i] && a[i] - b[i] < tol)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): structured loop with invariants outside the loop body for proper syntax */
  result := new bool[a.Length];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> result[j] == (-tol < a[j] - b[j] && a[j] - b[j] < tol)
  {
    if i < a.Length {
      result[i] := (-tol < a[i] - b[i] && a[i] - b[i] < tol);
    }
  }
}
// </vc-code>
