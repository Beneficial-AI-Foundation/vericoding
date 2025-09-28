// <vc-preamble>
// Method that implements numpy flat operation for 1D arrays
// For 1D arrays, this provides a view with the same elements in the same order
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method numpy_flat(a: array<real>) returns (result: array<real>)
  ensures result.Length == a.Length
  ensures forall i :: 0 <= i < a.Length ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
{
  result := new real[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> result[k] == a[k]
  {
    result[i] := a[i];
    i := i + 1;
  }
}
// </vc-code>
