// <vc-preamble>
// Method that computes the element-wise negative of an array of real numbers
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method NumpyNegative(x: array<real>) returns (result: array<real>)
  // No preconditions required for negation operation
  ensures result.Length == x.Length  // Result has same length as input
  ensures forall i :: 0 <= i < x.Length ==> result[i] == -x[i]  // Each element is negated
// </vc-spec>
// <vc-code>
{
  result := new real[x.Length];
  var i := 0;
  while i < x.Length
    invariant 0 <= i <= x.Length
    invariant forall j :: 0 <= j < i ==> result[j] == -x[j]
  {
    result[i] := -x[i];
    i := i + 1;
  }
}
// </vc-code>
