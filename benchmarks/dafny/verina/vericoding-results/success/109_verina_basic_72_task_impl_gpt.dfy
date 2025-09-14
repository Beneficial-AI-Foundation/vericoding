// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method Append(a: array<int>, b: int) returns (result: array<int>)
    ensures result.Length == a.Length + 1
    ensures forall i :: 0 <= i < a.Length ==> result[i] == a[i]
    ensures result[a.Length] == b
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  result := new int[n + 1];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result.Length == n + 1
    invariant forall k :: 0 <= k < i ==> result[k] == a[k]
  {
    result[i] := a[i];
    i := i + 1;
  }
  result[n] := b;
}
// </vc-code>
