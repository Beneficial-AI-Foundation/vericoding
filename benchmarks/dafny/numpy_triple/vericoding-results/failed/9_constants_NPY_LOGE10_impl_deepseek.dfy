// <vc-preamble>
// Looking at the error, Dafny doesn't support scientific notation like `1e-15`. I need to replace it with the decimal equivalent.



// Ghost function to represent absolute value for specification purposes
ghost function {:axiom} Abs(x: real): real
    ensures Abs(x) >= 0.0
    ensures Abs(x) == x || Abs(x) == -x
    ensures x >= 0.0 ==> Abs(x) == x
    ensures x < 0.0 ==> Abs(x) == -x
// Ghost function to represent the natural logarithm for specification purposes
ghost function {:axiom} RealLn(x: real): real
    requires x > 0.0
    // Standard mathematical properties of natural logarithm
    ensures x == 1.0 ==> RealLn(x) == 0.0  // ln(1) = 0
    ensures x > 1.0 ==> RealLn(x) > 0.0    // ln(x) > 0 when x > 1
    ensures x < 1.0 ==> RealLn(x) < 0.0    // ln(x) < 0 when x < 1
// </vc-preamble>

// <vc-helpers>
function approxln(x: real): real
  requires x > 0.0
  decreases if x <= 2.0 then 0 else x
{
  /* helper modified by LLM (iteration 5): Added decreases clause to ensure termination */
  if x == 1.0 then
    0.0
  else if x <= 2.0 then
    // Taylor series approximation around 1: ln(x) ≈ (x-1) - (x-1)^2/2 + (x-1)^3/3 - (x-1)^4/4 + (x-1)^5/5 - (x-1)^6/6
    var y := x - 1.0;
    y - (y*y)/2.0 + (y*y*y)/3.0 - (y*y*y*y)/4.0 + (y*y*y*y*y)/5.0 - (y*y*y*y*y*y)/6.0
  else
    // Use logarithmic property: ln(x) = ln(x/2) + ln(2) with termination measure
    approxln(x/2.0) + approxln(2.0)
}
// </vc-helpers>

// <vc-spec>
method NpyLoge10() returns (result: real)
    // No preconditions needed for mathematical constant
    ensures result > 0.0  // ln(10) is positive since 10 > 1
    ensures result > 1.0  // ln(10) > ln(e) = 1 since 10 > e  
    ensures result > 2.0 && result < 3.0  // ln(10) is between 2 and 3
    ensures result > 2.302 && result < 2.303  // Coarse bounds check
    ensures result > 2.30258 && result < 2.30259  // Precise bounds check
    // Mathematical property: result approximates ln(10) to high precision
    ensures Abs(result - 2.302585092994045684017991454684364208) < 0.000000000000001
    // Fundamental logarithmic property: e^result = 10 (represented as constraint)
    ensures result == RealLn(10.0)  // Direct mathematical definition
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Enhanced assertion proof with explicit calculations */
  // Compute ln(2.0) and ln(5.0) using recursive approximation
  var ln2: real := approxln(2.0);
  var ln5: real := approxln(5.0);
  
  // Calculate ln(10) = ln(2) + ln(5)
  result := ln2 + ln5;
  
  // Manual bounds verification for the assertion
  assert result > 2.30258 && result < 2.30259 by {
    // Explicitly compute Taylor approximations with known values
    // ln(2) calculation: taylor(2.0) = (1.0) - (1.0)/2 + (1.0)/3 - (1.0)/4 + (1.0)/5 - (1.0)/6
    var ln2_calc := 1.0 - 0.5 + 1.0/3.0 - 0.25 + 0.2 - 1.0/6.0;
    // ln(5) calculation: taylor(5.0) requires recursive: taylor(2.5) + taylor(2.0)
    var y := 5.0 / 2.0 / 2.0 - 1.0; // 5/2/2 = 1.25, so y = 0.25
    var ln125 := y - (y*y)/2.0 + (y*y*y)/3.0 - (y*y*y*y)/4.0 + (y*y*y*y*y)/5.0 - (y*y*y*y*y*y)/6.0;
    var ln25 := ln125 + ln2_calc;
    var ln5_calc := ln25 + ln2_calc;
    var total := ln2_calc + ln5_calc;
    assert total > 2.30258 && total < 2.30259;
  }
}
// </vc-code>
