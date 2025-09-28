// <vc-preamble>
/*
 * Dafny specification for numpy.sign function
 * Returns an element-wise indication of the sign of a number.
 * For each element: returns -1 if negative, 0 if zero, 1 if positive.
 */

// Method to compute element-wise sign of floating point numbers
// </vc-preamble>

// <vc-helpers>

function real_lt(a: real, b: real): bool { a < b }
function real_eq(a: real, b: real): bool { a == b }
function real_gt(a: real, b: real): bool { a > b }
predicate valid_index(arr: array<real>, i: int) { 0 <= i < arr.Length }

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
  while i < result.Length
    invariant 0 <= i <= result.Length
    invariant result.Length == x.Length
    invariant forall j :: 0 <= j < i ==> (
      (x[j] < 0.0 ==> result[j] == -1.0) &&
      (x[j] == 0.0 ==> result[j] == 0.0) &&
      (x[j] > 0.0 ==> result[j] == 1.0)
    )
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
