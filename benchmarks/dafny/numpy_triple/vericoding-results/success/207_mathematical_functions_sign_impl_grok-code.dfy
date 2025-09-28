// <vc-preamble>
/*
 * Dafny specification for numpy.sign function
 * Returns an element-wise indication of the sign of a number.
 * For each element: returns -1 if negative, 0 if zero, 1 if positive.
 */

// Method to compute element-wise sign of floating point numbers
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 3): add loop invariant to correctly set element-wise signs */
  var res := new real[x.Length];
  for i := 0 to x.Length
    invariant 0 <= i <= x.Length
    invariant forall k :: 0 <= k < i ==>
      (x[k] < 0.0 ==> res[k] == -1.0) &&
      (x[k] == 0.0 ==> res[k] == 0.0) &&
      (x[k] > 0.0 ==> res[k] == 1.0)
  {
    if x[i] < 0.0 {
      res[i] := -1.0;
    } else if x[i] > 0.0 {
      res[i] := 1.0;
    } else {
      res[i] := 0.0;
    }
  }
  result := res;
}
// </vc-code>
