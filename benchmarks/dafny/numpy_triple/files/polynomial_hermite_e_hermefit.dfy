// <vc-preamble>
// Helper function to evaluate probabilist's Hermite polynomials He_n(x)
function HermiteE(n: nat, x: real): real
  decreases n
{
  if n == 0 then 1.0
  else if n == 1 then x
  else x * HermiteE(n-1, x) - (n-1) as real * HermiteE(n-2, x)
}

// Predicate to check if a real number is finite (not NaN or infinite)
predicate IsFinite(r: real) {
  true // In Dafny, reals are always finite by definition
}

// Function to evaluate a Hermite series at a given point
function EvaluateHermiteSeries(coeffs: seq<real>, x: real): real
  requires |coeffs| > 0
{
  if |coeffs| == 1 then coeffs[0]
  else coeffs[0] + coeffs[1] * HermiteE(1, x) + 
       EvaluateHermiteSeriesRec(coeffs[2..], x, 2)
}

// Recursive helper for series evaluation
function EvaluateHermiteSeriesRec(coeffs: seq<real>, x: real, start_degree: nat): real
  decreases |coeffs|
{
  if |coeffs| == 0 then 0.0
  else coeffs[0] * HermiteE(start_degree, x) + 
       EvaluateHermiteSeriesRec(coeffs[1..], x, start_degree + 1)
}

// Function to compute sum of squared residuals
function SumSquaredResiduals(x_vals: seq<real>, y_vals: seq<real>, coeffs: seq<real>): real
  requires |x_vals| == |y_vals|
  requires |coeffs| > 0
  requires |x_vals| > 0
{
  SumSquaredResidualsRec(x_vals, y_vals, coeffs, 0)
}

// Recursive helper for computing sum of squared residuals
function SumSquaredResidualsRec(x_vals: seq<real>, y_vals: seq<real>, coeffs: seq<real>, index: nat): real
  requires |x_vals| == |y_vals|
  requires |coeffs| > 0
  requires index <= |x_vals|
  decreases |x_vals| - index
{
  if index >= |x_vals| then 0.0
  else
    var predicted := EvaluateHermiteSeries(coeffs, x_vals[index]);
    var residual := y_vals[index] - predicted;
    residual * residual + SumSquaredResidualsRec(x_vals, y_vals, coeffs, index + 1)
}

// Function to compute dot product of two sequences
function DotProduct(seq1: seq<real>, seq2: seq<real>): real
  requires |seq1| == |seq2|
{
  if |seq1| == 0 then 0.0
  else seq1[0] * seq2[0] + DotProduct(seq1[1..], seq2[1..])
}

// Function to compute residuals
function ComputeResiduals(x_vals: seq<real>, y_vals: seq<real>, coeffs: seq<real>): seq<real>
  requires |x_vals| == |y_vals|
  requires |coeffs| > 0
  requires |x_vals| > 0
  ensures |ComputeResiduals(x_vals, y_vals, coeffs)| == |x_vals|
{
  seq(|x_vals|, i requires 0 <= i < |x_vals| => 
    y_vals[i] - EvaluateHermiteSeries(coeffs, x_vals[i]))
}

// Function to compute basis function values at all x points for degree k
function BasisValues(x_vals: seq<real>, k: nat): seq<real>
  requires |x_vals| > 0
  ensures |BasisValues(x_vals, k)| == |x_vals|
{
  seq(|x_vals|, i requires 0 <= i < |x_vals| => HermiteE(k, x_vals[i]))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method HermeFit(x_vals: seq<real>, y_vals: seq<real>, degree: nat) 
  returns (coefficients: seq<real>)
  requires |x_vals| == |y_vals|  // x and y must have same length
  requires |x_vals| > 0          // must have at least one data point
  requires degree + 1 <= |x_vals| // degree constraint for solvability
  requires forall i :: 0 <= i < |x_vals| ==> IsFinite(x_vals[i]) // x values are finite
  requires forall i :: 0 <= i < |y_vals| ==> IsFinite(y_vals[i]) // y values are finite
  
  ensures |coefficients| == degree + 1  // output has correct size
  
  // All coefficients are finite
  ensures forall i :: 0 <= i < |coefficients| ==> IsFinite(coefficients[i])
  
  // Least squares optimality: coefficients minimize sum of squared residuals
  ensures forall other_coeffs: seq<real> :: 
    |other_coeffs| == degree + 1 ==>
    SumSquaredResiduals(x_vals, y_vals, coefficients) <= 
    SumSquaredResiduals(x_vals, y_vals, other_coeffs)
  
  // Exact interpolation when we have exactly degree+1 points
  ensures degree + 1 == |x_vals| ==> 
    forall i :: 0 <= i < |x_vals| ==> 
      var predicted := EvaluateHermiteSeries(coefficients, x_vals[i]);
      (y_vals[i] - predicted) * (y_vals[i] - predicted) < 0.00000000000000000001
  
  // Orthogonality condition: residuals are orthogonal to basis functions
  ensures forall k :: 0 <= k <= degree ==>
    var residuals := ComputeResiduals(x_vals, y_vals, coefficients);
    var basis_vals := BasisValues(x_vals, k);
    var dot_prod := DotProduct(residuals, basis_vals);
    dot_prod * dot_prod < 0.00000000000000000001
  
  // Consistency: if all y values are zero, then all coefficients should be zero
  ensures (forall i :: 0 <= i < |y_vals| ==> y_vals[i] == 0.0) ==>
    (forall i :: 0 <= i < |coefficients| ==> coefficients[i] == 0.0)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
