// <vc-preamble>
function IntPow(base: int, exp: nat): int
    decreases exp
{
    if exp == 0 then
        1
    else
        base * IntPow(base, exp - 1)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Power(a: array<int>, b: array<nat>) returns (result: array<int>)
    requires a.Length == b.Length
    ensures 
        result.Length == a.Length &&
        forall i :: 0 <= i < a.Length ==> result[i] == IntPow(a[i], b[i])
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  result := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant n == a.Length
    invariant n == b.Length
    invariant result.Length == n
    invariant forall j :: 0 <= j < i ==> result[j] == IntPow(a[j], b[j])
    decreases n - i
  {
    result[i] := IntPow(a[i], b[i]);
    i := i + 1;
  }
}
// </vc-code>
