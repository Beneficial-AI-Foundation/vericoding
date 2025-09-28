// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): simple predicate to check closeness within tolerance */
function IsClose(d: int, tol: int): bool
{
  -tol < d && d < tol
}
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
  /* code modified by LLM (iteration 2): remove null-check invariant and implement loop using IsClose */
  result := new bool[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result.Length == a.Length
    invariant forall j :: 0 <= j < i ==> result[j] == IsClose(a[j] - b[j], tol)
  {
    result[i] := IsClose(a[i] - b[i], tol);
    i := i + 1;
  }
}
// </vc-code>
