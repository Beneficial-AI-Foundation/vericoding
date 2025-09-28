// <vc-preamble>
// Method to compute cube root of each element in an array
// </vc-preamble>

// <vc-helpers>
function cbrt_helper(r: real): (y: real)
  // Precondition: input is non-negative
  requires r >= 0.0
  // Specification: cube root property
  ensures y * y * y == r
{
  // Approximation algorithm for cube root
  if r == 0.0 then 0.0
  else {
    var y := 1.0;
    var prev := 0.0;
    var count := 0;
    while y != prev && count < 1000
      invariant y >= 0.0
      invariant count <= 1000
      invariant y * y * y <= r || count == 0
      decreases 1000 - count
    {
      prev := y;
      y := (2.0 * y + r / (y * y)) / 3.0;
      count := count + 1;
    }
    y
  }
}

/* helper modified by LLM (iteration 5): Fixed while loop condition syntax */
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
  /* code modified by LLM (iteration 5): Fixed while loop condition syntax */
  result := new real[x.Length];
  var i := 0;
  while i < x.Length
    invariant 0 <= i <= x.Length
    invariant result.Length == x.Length
    invariant forall j :: 0 <= j < i ==> result[j] * result[j] * result[j] == x[j]
  {
    // Cube root handles both positive and negative numbers
    if x[i] >= 0.0 {
      result[i] := cbrt_helper(x[i]);
    } else {
      result[i] := -cbrt_helper(-x[i]);
    }
    i := i + 1;
  }
}
// </vc-code>
