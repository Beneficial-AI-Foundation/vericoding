// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function IdInt(x: int): int { x }
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
    invariant forall j :: 0 <= j < i ==> result[j] == a[j]
    invariant a.Length == n
    decreases n - i
  {
    result[i] := a[i];
    i := i + 1;
  }
  result[n] := b;
}
// </vc-code>
