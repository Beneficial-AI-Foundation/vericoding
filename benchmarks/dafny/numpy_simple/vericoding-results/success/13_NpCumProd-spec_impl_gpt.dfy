// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function prodStep(prev: int, ai: int): int { prev * ai }
// </vc-helpers>

// <vc-spec>
method CumProd(a: array<int>) returns (result: array<int>)
    requires a.Length > 0
    ensures 
        result.Length == a.Length &&
        result[0] == a[0] &&
        forall i :: 0 < i < a.Length ==> result[i] == result[i-1] * a[i]
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  result := new int[n];
  result[0] := a[0];
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant n == a.Length
    invariant result.Length == n
    invariant result[0] == a[0]
    invariant forall j :: 1 <= j < i ==> result[j] == result[j-1] * a[j]
    decreases n - i
  {
    result[i] := result[i-1] * a[i];
    i := i + 1;
  }
}
// </vc-code>
