// <vc-preamble>
// Method to compute cube root of each element in an array
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed function declaration and while loop condition */
function cbrt_single(x: real): real
  // Returns cube root of x
  ensures cbrt_single(x) * cbrt_single(x) * cbrt_single(x) == x
{
  if x == 0.0 then 0.0 else
  if x > 0.0 then
    // For positive x, binary search for cube root
    var low, high := 0.0, if x < 1.0 then 1.0 else x;
    while high - low > 1e-10
      invariant low <= high
      invariant low * low * low <= x <= high * high * high
    {
      var mid := (low + high) / 2.0;
      if mid * mid * mid < x then
        low := mid;
      else
        high := mid;
    }
    low
  else
    // For negative x, find positive cube root and negate
    -cbrt_single(-x)
}
// </vc-helpers>

// <vc-spec>
method cbrt(x: array<real>) returns (result: array<real>)
  // Postconditions: result array properties
  ensures result.Length == x.Length
  // Core specification: each result element is the cube root of corresponding input element
  ensures forall i :: 0 <= i < result.Length ==> 
    result[i] * result[i] * result[i] == x[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): using fixed helper function */
  result := new real[x.Length];
  for i := 0 to x.Length
    invariant 0 <= i <= x.Length
    invariant forall j :: 0 <= j < i ==> result[j] * result[j] * result[j] == x[j]
  {
    result[i] := cbrt_single(x[i]);
  }
}
// </vc-code>
