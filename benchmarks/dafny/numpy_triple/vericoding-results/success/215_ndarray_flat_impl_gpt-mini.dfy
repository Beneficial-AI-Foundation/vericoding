// <vc-preamble>
// Method that implements numpy flat operation for 1D arrays
// For 1D arrays, this provides a view with the same elements in the same order
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): removed null checks because arrays are non-nullable */
predicate ArraysEqual(a: array<real>, b: array<real>)
  reads a, b
  { a.Length == b.Length && (forall i :: 0 <= i < a.Length ==> a[i] == b[i]) }
// </vc-helpers>

// <vc-spec>
method numpy_flat(a: array<real>) returns (result: array<real>)
  ensures result.Length == a.Length
  ensures forall i :: 0 <= i < a.Length ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implemented numpy_flat by allocating and copying elements */
  result := new real[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result.Length == a.Length
    invariant forall j :: 0 <= j < i ==> result[j] == a[j]
  {
    result[i] := a[i];
    i := i + 1;
  }
}
// </vc-code>
