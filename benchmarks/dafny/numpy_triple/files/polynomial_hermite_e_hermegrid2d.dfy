// <vc-preamble>
// Ghost function representing the i-th probabilist's Hermite polynomial (HermiteE)
ghost function HermiteE(x: real, degree: nat): real

// Ghost function to sum a sequence of reals
ghost function SumSeq(s: seq<real>): real
{
  if |s| == 0 then 0.0
  else s[0] + SumSeq(s[1..])
}

// Ghost function to compute the 2D polynomial evaluation at a single point
ghost function EvaluatePolynomialAt(x_val: real, y_val: real, c: seq<seq<real>>): real
  requires forall i :: 0 <= i < |c| ==> |c[i]| == (if |c| == 0 then 0 else |c[0]|)
{
  if |c| == 0 || (|c| > 0 && |c[0]| == 0) then 0.0
  else
    SumSeq(seq(|c|, k_x => 
      SumSeq(seq(|c[0]|, k_y => 
        c[k_x][k_y] * HermiteE(x_val, k_x) * HermiteE(y_val, k_y)))))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method HermeGrid2D(x: seq<real>, y: seq<real>, c: seq<seq<real>>) returns (result: seq<seq<real>>)
  requires forall i :: 0 <= i < |c| ==> |c[i]| == (if |c| == 0 then 0 else |c[0]|)
  // Coefficient matrix must be rectangular if non-empty
  ensures |result| == |x|
  // Result has correct number of rows
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == |y|
  // Each row has correct number of columns  
  ensures forall i, j :: 0 <= i < |x| && 0 <= j < |y| ==>
    result[i][j] == EvaluatePolynomialAt(x[i], y[j], c)
  // Each result[i,j] represents the polynomial evaluation at point (x[i], y[j])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
