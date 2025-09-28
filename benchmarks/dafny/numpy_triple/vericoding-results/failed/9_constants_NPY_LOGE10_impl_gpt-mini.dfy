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
/* helper modified by LLM (iteration 5): lemma that RealLn(10.0) > 0.0 */
lemma LnTenPositive()
  ensures RealLn(10.0) > 0.0
{
  // From RealLn specification: for x > 1.0, RealLn(x) > 0.0
  assert 10.0 > 1.0;
  assert RealLn(10.0) > 0.0;
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
  /* code modified by LLM (iteration 5): return RealLn(10.0) and invoke lemma proving positivity */
  LnTenPositive();
  result := RealLn(10.0);
}

// </vc-code>
