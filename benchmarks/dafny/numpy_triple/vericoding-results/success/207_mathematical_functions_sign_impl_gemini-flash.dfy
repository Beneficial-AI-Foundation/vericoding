// <vc-preamble>
/*
 * Dafny specification for numpy.sign function
 * Returns an element-wise indication of the sign of a number.
 * For each element: returns -1 if negative, 0 if zero, 1 if positive.
 */

// Method to compute element-wise sign of floating point numbers
// </vc-preamble>

// <vc-helpers>
predicate IsSign(r: real) { r == -1.0 || r == 0.0 || r == 1.0 }
// </vc-helpers>

// <vc-spec>
method sign(x: array<real>) returns (result: array<real>)
  ensures result.Length == x.Length
  // Element-wise sign specification: -1 for negative, 0 for zero, 1 for positive
  ensures forall i :: 0 <= i < result.Length ==>
    (x[i] < 0.0 ==> result[i] == -1.0) &&
    (x[i] == 0.0 ==> result[i] == 0.0) &&
    (x[i] > 0.0 ==> result[i] == 1.0)
// </vc-spec>
// <vc-code>
{
  result := new real[x.Length];
  var i: int := 0;
  while i < x.Length
    invariant 0 <= i <= x.Length
    invariant forall k :: 0 <= k < i ==> IsSign(result[k])
    invariant forall k :: 0 <= k < i ==> ( (x[k] < 0.0 ==> result[k] == -1.0) && (x[k] == 0.0 ==> result[k] == 0.0) && (x[k] > 0.0 ==> result[k] == 1.0) )
  {
    if x[i] < 0.0 {
      result[i] := -1.0;
    } else if x[i] == 0.0 {
      result[i] := 0.0;
    } else {
      result[i] := 1.0;
    }
    i := i + 1;
  }
}
// </vc-code>
