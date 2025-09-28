// <vc-preamble>
// Method that implements numpy flat operation for 1D arrays
// For 1D arrays, this provides a view with the same elements in the same order
// </vc-preamble>

// <vc-helpers>
function InRangeLen(len: int, i: int): bool { 0 <= i && i < len }
// </vc-helpers>

// <vc-spec>
method numpy_flat(a: array<real>) returns (result: array<real>)
  ensures result.Length == a.Length
  ensures forall i :: 0 <= i < a.Length ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
{
  result := a;
}
// </vc-code>
