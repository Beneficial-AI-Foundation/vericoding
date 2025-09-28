// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// No helpers needed for this problem.
// </vc-helpers>

// <vc-spec>
method BitwiseOr(a: array<bv32>, b: array<bv32>) returns (result: array<bv32>)
    requires a.Length == b.Length
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < result.Length ==> result[i] == (a[i] | b[i])
// </vc-spec>
// <vc-code>
{
  result := new bv32[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> result[k] == (a[k] | b[k])
  {
    result[i] := a[i] | b[i];
    i := i + 1;
  }
  return result;
}
// </vc-code>
