// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function getDiff(a: array<int>, b: array<int>, i: int): int
  requires 0 <= i < a.Length
  requires a.Length == b.Length
  reads a, b
  ensures getDiff(a, b, i) == a[i] - b[i]
{
  a[i] - b[i]
}
// </vc-helpers>

// <vc-spec>
method subtract(a: array<int>, b: array<int>) returns (result: array<int>)
    requires a.Length == b.Length
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> result[i] == a[i] - b[i]
// </vc-spec>
// <vc-code>
{
  result := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> result[j] == a[j] - b[j]
    invariant result.Length == a.Length
  {
    result[i] := a[i] - b[i];
    i := i + 1;
  }
}
// </vc-code>
