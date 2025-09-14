// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function prod(x: int, y: int): int { x * y }
// </vc-helpers>

// <vc-spec>
method ArrayProduct(a: array<int>, b: array<int>) returns (result: array<int>)
    requires a.Length == b.Length
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> result[i] == a[i] * b[i]
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  var res := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> res[k] == a[k] * b[k]
  {
    res[i] := a[i] * b[i];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
