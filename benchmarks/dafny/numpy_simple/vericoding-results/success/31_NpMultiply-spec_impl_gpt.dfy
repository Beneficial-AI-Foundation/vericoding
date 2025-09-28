// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function prod(x: int, y: int): int { x * y }
// </vc-helpers>

// <vc-spec>
method multiply(a: array<int>, b: array<int>) returns (result: array<int>)
    requires a.Length == b.Length
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> result[i] == a[i] * b[i]
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  result := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result.Length == n
    invariant n == a.Length
    invariant n == b.Length
    invariant forall j :: 0 <= j < i ==> result[j] == a[j] * b[j]
    decreases n - i
  {
    result[i] := prod(a[i], b[i]);
    i := i + 1;
  }
}
// </vc-code>
