// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function InBounds(a: array<int>, i: int): bool { 0 <= i < a.Length }
// </vc-helpers>

// <vc-spec>
method LessEqual(a: array<int>, b: array<int>) returns (result: array<bool>)
    requires a.Length == b.Length
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> result[i] == (a[i] <= b[i])
// </vc-spec>
// <vc-code>
{
  result := new bool[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result.Length == a.Length
    invariant forall k :: 0 <= k < i ==> result[k] == (a[k] <= b[k])
    decreases a.Length - i
  {
    result[i] := a[i] <= b[i];
    i := i + 1;
  }
}
// </vc-code>
