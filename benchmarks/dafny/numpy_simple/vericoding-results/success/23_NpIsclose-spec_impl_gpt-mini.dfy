// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function IsClose(x: int, y: int, tol: int): bool { -tol < x - y && x - y < tol }
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
  var n := a.Length;
  result := new bool[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result.Length == n
    invariant forall j :: 0 <= j < i ==> result[j] == IsClose(a[j], b[j], tol)
  {
    result[i] := IsClose(a[i], b[i], tol);
    i := i + 1;
  }
}
// </vc-code>
