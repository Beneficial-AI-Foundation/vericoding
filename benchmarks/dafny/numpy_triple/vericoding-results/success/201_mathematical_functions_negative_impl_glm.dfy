// <vc-preamble>
// Method that computes the element-wise negative of an array of real numbers
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
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
  for i := 0 to x.Length
  invariant 0 <= i <= x.Length
  invariant forall j :: 0 <= j < i ==> result[j] == -x[j]
  {
    if i < x.Length {
      result[i] := -x[i];
    }
  }
}
// </vc-code>
