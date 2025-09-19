// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Poly2Cheb(pol: seq<real>) returns (result: seq<real>)
  requires |pol| >= 0
  ensures |result| == |pol|
  
  // Specific test case from documentation: [0, 1, 2, 3] → [1, 3.25, 1, 0.75]
  ensures |pol| == 4 && pol[0] == 0.0 && pol[1] == 1.0 && pol[2] == 2.0 && pol[3] == 3.0 ==>
          result[0] == 1.0 && result[1] == 3.25 && result[2] == 1.0 && result[3] == 0.75
  
  // Identity property: constant polynomial [c, 0, ..., 0] yields [c, 0, ..., 0]
  ensures |pol| > 0 ==> 
          (forall i :: 1 <= i < |pol| ==> pol[i] == 0.0) ==>
          (forall i :: 1 <= i < |result| ==> result[i] == 0.0) && result[0] == pol[0]
  
  // Linear polynomial property: [a, b, 0, ..., 0] preserves first two coefficients
  ensures |pol| > 1 ==>
          (forall i :: 2 <= i < |pol| ==> pol[i] == 0.0) ==>
          result[0] == pol[0] && result[1] == pol[1]
  
  // Mathematical property: quadratic polynomial x² conversion [0, 0, 1] → [0.5, 0, 0.5]
  ensures |pol| == 3 && pol[0] == 0.0 && pol[1] == 0.0 && pol[2] == 1.0 ==>
          result[0] == 0.5 && result[1] == 0.0 && result[2] == 0.5
  
  // Mathematical property: cubic polynomial x³ conversion [0, 0, 0, 1] → [0, 0.75, 0, 0.25]
  ensures |pol| == 4 && pol[0] == 0.0 && pol[1] == 0.0 && pol[2] == 0.0 && pol[3] == 1.0 ==>
          result[0] == 0.0 && result[1] == 0.75 && result[2] == 0.0 && result[3] == 0.25
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
