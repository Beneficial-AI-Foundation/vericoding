// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method NumpySquare(x: array<real>) returns (result: array<real>)
  // The result array has the same length as the input
  ensures result.Length == x.Length
  // Each element in result is the square of the corresponding element in x
  ensures forall i :: 0 <= i < x.Length ==> result[i] == x[i] * x[i]
  // All result elements are non-negative (follows from squaring property)
  ensures forall i :: 0 <= i < result.Length ==> result[i] >= 0.0
  // Preserves zeros: if input element is zero, result element is zero
  ensures forall i :: 0 <= i < x.Length && x[i] == 0.0 ==> result[i] == 0.0
// </vc-spec>
// <vc-code>
{
  result := new real[x.Length];
  var i := 0;
  while i < x.Length
    invariant 0 <= i <= x.Length
    invariant forall j :: 0 <= j < i ==> result[j] == x[j] * x[j]
    invariant forall j :: 0 <= j < i ==> result[j] >= 0.0
    invariant forall j :: 0 <= j < i && x[j] == 0.0 ==> result[j] == 0.0
  {
    result[i] := x[i] * x[i];
    i := i + 1;
  }
}
// </vc-code>
