// <vc-preamble>
// Method to multiply two Chebyshev series
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ChebMul(c1: seq<real>, c2: seq<real>) returns (result: seq<real>)
  requires |c1| > 0 && |c2| > 0  // Input series must be non-empty
  ensures |result| == |c1| + |c2| - 1  // Result length is sum of input lengths minus 1
  
  // Property: multiplying by a constant polynomial [a] scales all coefficients appropriately
  ensures |c2| == 1 ==> forall i :: 0 <= i < |c1| ==> result[i] == c2[0] * c1[i]
  
  // Property: multiplying by T_0 (represented as [1]) preserves the other polynomial
  ensures |c1| == 1 && c1[0] == 1.0 ==> 
    forall j :: 0 <= j < |c2| ==> result[j] == c2[j]
  
  // Property: multiplying T_0 by any polynomial preserves it in the result
  ensures |c2| == 1 && c2[0] == 1.0 ==> 
    forall i :: 0 <= i < |c1| ==> result[i] == c1[i]
  
  // Special case: multiplication of two linear polynomials [a,b] * [c,d]
  // Based on Chebyshev multiplication rule: T_m * T_n = (T_{m+n} + T_{|m-n|}) / 2
  ensures |c1| == 2 && |c2| == 2 ==> 
    var a, b, c, d := c1[0], c1[1], c2[0], c2[1];
    result[0] == a * c + b * d / 2.0 &&  // Constant term
    result[1] == a * d + b * c &&        // Linear term  
    result[2] == b * d / 2.0             // Quadratic term
  
  // Verification of the documented example: [1,2,3] * [3,2,1] = [6.5, 12, 12, 4, 1.5]
  ensures |c1| == 3 && |c2| == 3 &&
          c1[0] == 1.0 && c1[1] == 2.0 && c1[2] == 3.0 &&
          c2[0] == 3.0 && c2[1] == 2.0 && c2[2] == 1.0 ==>
    result[0] == 6.5 &&
    result[1] == 12.0 &&
    result[2] == 12.0 &&
    result[3] == 4.0 &&
    result[4] == 1.5
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
