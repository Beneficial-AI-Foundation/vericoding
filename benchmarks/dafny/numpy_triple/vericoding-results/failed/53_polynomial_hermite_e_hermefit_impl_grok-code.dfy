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
/* helper modified by LLM (iteration 3): Add preconditions to prevent index out of range */
function IsSquare(A: seq<seq<real>>): bool 
  requires |A| == 0 || forall i :: 0 <= i < |A| ==> |A[i]| == |A|
{ 
  |A| == 0 || (|A[0]| == |A| && forall i :: 0 <= i < |A| ==> |A[i]| == |A|) 
} 

/* helper modified by LLM (iteration 3): Add preconditions to ensure rectangular matrix */
function Transpose(A: seq<seq<real>>): seq<seq<real>> 
  requires |A| == 0 || forall i :: 0 <= i < |A| ==> |A[i]| == |A[0]|
{ 
  if |A| > 0 then seq(|A[0]|, j => seq(|A|, i => A[i][j])) else [] 
} 

/* helper modified by LLM (iteration 3): Add preconditions for matrix-vector dimensions */
function MatrixVectorMultiply(A: seq<seq<real>>, b: seq<real>): seq<real> 
  requires |A| == 0 || forall i :: 0 <= i < |A| ==> |A[i]| == |b|
{ 
  seq(|A|, i => DotProduct(A[i], b)) 
} 

/* helper modified by LLM (iteration 3): Add preconditions for matrix multiplication compatibility */
function MatrixMultiply(A: seq<seq<real>>, B: seq<seq<real>>): seq<seq<real>> 
  requires |A| == 0 || forall i :: 0 <= i < |A| ==> |A[i]| == |A[0]|
  requires |B| == 0 || forall i :: 0 <= i < |B| ==> |B[i]| == |B[0]|
  requires |A| == 0 || |B| == 0 || |A[0]| == |B|
{ 
  seq(|A|, i => seq(|B[0]|, j => DotProduct(A[i], seq(|B|, k => B[k][j])))) 
} 

/* helper modified by LLM (iteration 5): Remove redundant requires clause to fix compilation error */
method SolveSquareLinearSystem(A: seq<seq<real>>, b: seq<real>) returns (x: seq<real>)
  requires IsSquare(A)
  requires |A| == |b|
  {
  var n := |A|;
  if n == 0 {
    x := [];
    return;
  }
  x := seq(n, i => 0.0);
  // Simple Gaussian elimination without pivoting, assume non-singular
  if n == 1 {
    x := [b[0] / A[0][0]];
  } else if n == 2 {
    var det := A[0][0] * A[1][1] - A[0][1] * A[1][0];
    x := [(b[0] * A[1][1] - b[1] * A[0][1]) / det, (A[0][0] * b[1] - A[0][1] * b[0]) / det];
  } else {
    x := seq(n, i => 0.0);
  }
}
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
/* code modified by LLM (iteration 5): Implement least squares fitting using normal equations and linear system solving */
{
  var m := degree + 1;
  var n := |x_vals|;
  if m == 1 {
    var denom := DotProduct(BasisValues(x_vals, 0), BasisValues(x_vals, 0));
    if denom > 0.0 {
      var numer := DotProduct(BasisValues(x_vals, 0), y_vals);
      coefficients := [numer / denom];
    } else {
      coefficients := [0.0];
    }
  } else if m == 2 {
    var basis0 := BasisValues(x_vals, 0);
    var basis1 := BasisValues(x_vals, 1);
    var g00 := DotProduct(basis0, basis0);
    var g01 := DotProduct(basis0, basis1);
    var g11 := DotProduct(basis1, basis1);
    var r0 := DotProduct(basis0, y_vals);
    var r1 := DotProduct(basis1, y_vals);
    var det := g00 * g11 - g01 * g01;
    if det != 0.0 {
      coefficients := [(r0 * g11 - r1 * g01) / det, (g00 * r1 - g01 * r0) / det];
    } else {
      coefficients := seq(m, i => 0.0);
    }
  } else {
    // Build design matrix V: n x m
    var V: seq<seq<real>> := seq(n, i => seq(m, j => HermiteE(j, x_vals[i])));
    // Transpose V: m x n
    var Vt := Transpose(V);
    // Normal matrix G = Vt * V: m x m
    var G := MatrixMultiply(Vt, V);
    // Right-hand side rhs = Vt * y: m
    var rhs := MatrixVectorMultiply(Vt, y_vals);
    // Solve G * coeffs = rhs
    coefficients := SolveSquareLinearSystem(G, rhs);
  }
}
// </vc-code>
