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
/* helper modified by LLM (iteration 5): compute minor by removing given row and column */
function Minor(mat: seq<seq<real>>, row: nat, col: nat): seq<seq<real>>
  requires |mat| > 0
  requires forall r :: 0 <= r < |mat| ==> |mat[r]| == |mat|
  requires row < |mat|
  requires col < |mat|
  decreases |mat|
{
  var n := |mat|;
  seq(n - 1, ii requires 0 <= ii < n - 1 =>
    var orig_row := if ii < row then ii else ii + 1;
    seq(n - 1, jj requires 0 <= jj < n - 1 =>
      var orig_col := if jj < col then jj else jj + 1;
      mat[orig_row][orig_col]
    )
  )
}

/* helper modified by LLM (iteration 5): determinant expansion sum along first row */
function DeterminantSum(mat: seq<seq<real>>, j: nat): real
  requires |mat| > 1
  requires forall r :: 0 <= r < |mat| ==> |mat[r]| == |mat|
  requires j <= |mat|
  decreases |mat|, |mat| - j
{
  if j >= |mat| then 0.0
  else
    var sign := if j % 2 == 0 then 1.0 else -1.0;
    sign * mat[0][j] * Determinant(Minor(mat, 0, j)) + DeterminantSum(mat, j + 1)
}

/* helper modified by LLM (iteration 5): top-level determinant with base case for 1x1 matrices */
function Determinant(mat: seq<seq<real>>): real
  requires |mat| > 0
  requires forall r :: 0 <= r < |mat| ==> |mat[r]| == |mat|
  decreases |mat|
{
  if |mat| == 1 then mat[0][0]
  else DeterminantSum(mat, 0)
}

/* helper modified by LLM (iteration 5): cofactor matrix, handles 1x1 specially */
function CofactorMatrix(mat: seq<seq<real>>): seq<seq<real>>
  requires |mat| > 0
  requires forall r :: 0 <= r < |mat| ==> |mat[r]| == |mat|
  decreases |mat|
{
  var n := |mat|;
  if n == 1 then
    seq(1, i requires 0 <= i < 1 => seq(1, j requires 0 <= j < 1 => 1.0))
  else
    seq(n, i requires 0 <= i < n =>
      seq(n, j requires 0 <= j < n =>
        var sign := if ((i + j) % 2) == 0 then 1.0 else -1.0;
        sign * Determinant(Minor(mat, i, j))
      )
    )
}

/* helper modified by LLM (iteration 5): transpose of a square matrix */
function Transpose(mat: seq<seq<real>>): seq<seq<real>>
  requires |mat| > 0
  requires forall r :: 0 <= r < |mat| ==> |mat[r]| == |mat|
  decreases |mat|
{
  var n := |mat|;
  seq(n, i requires 0 <= i < n => seq(n, j requires 0 <= j < n => mat[j][i]))
}

/* helper modified by LLM (iteration 5): adjugate via transpose of cofactor matrix */
function Adjugate(mat: seq<seq<real>>): seq<seq<real>>
  requires |mat| > 0
  requires forall r :: 0 <= r < |mat| ==> |mat[r]| == |mat|
  decreases |mat|
{
  Transpose(CofactorMatrix(mat))
}

/* helper modified by LLM (iteration 5): replace a column in a square matrix */
function ReplaceColumn(mat: seq<seq<real>>, col: nat, newCol: seq<real>): seq<seq<real>>
  requires |mat| > 0
  requires forall r :: 0 <= r < |mat| ==> |mat[r]| == |mat|
  requires |newCol| == |mat|
  requires col < |mat|
  decreases |mat|
{
  var n := |mat|;
  seq(n, i requires 0 <= i < n =>
    seq(n, j requires 0 <= j < n =>
      if j == col then newCol[i] else mat[i][j]
    )
  )
}

/* helper modified by LLM (iteration 5): matrix-vector multiplication for square matrix */
function MatrixVectorMul(mat: seq<seq<real>>, vec: seq<real>): seq<real>
  requires |mat| > 0
  requires forall r :: 0 <= r < |mat| ==> |mat[r]| == |mat|
  requires |vec| == |mat|
  decreases |mat|
{
  var n := |mat|;
  seq(n, i requires 0 <= i < n => DotProduct(mat[i], vec))
}

/* helper modified by LLM (iteration 5): divide each element of a sequence by scalar (s != 0) */
function ScalarDivSeq(vec: seq<real>, s: real): seq<real>
  requires |vec| >= 0
  requires s != 0.0
  decreases |vec|
{
  seq(|vec|, i requires 0 <= i < |vec| => vec[i] / s)
}

/* helper modified by LLM (iteration 5): solve linear system using Cramer's rule (requires non-singular matrix) */
function SolveLinearSystemCramer(mat: seq<seq<real>>, rhs: seq<real>): seq<real>
  requires |mat| > 0
  requires forall r :: 0 <= r < |mat| ==> |mat[r]| == |mat|
  requires |rhs| == |mat|
  requires Determinant(mat) != 0.0
  decreases |mat|
{
  var n := |mat|;
  var det := Determinant(mat);
  seq(n, i requires 0 <= i < n => Determinant(ReplaceColumn(mat, i, rhs)) / det)
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
/* code modified by LLM (iteration 5): build normal equations and solve with Cramer's rule (requires Gram matrix non-singular) */
{
  var n := degree + 1;
  var G := seq(n, i requires 0 <= i < n =>
    seq(n, j requires 0 <= j < n => DotProduct(BasisValues(x_vals, i), BasisValues(x_vals, j)))
  );
  var g := seq(n, i requires 0 <= i < n => DotProduct(BasisValues(x_vals, i), y_vals));
  var detG := Determinant(G);
  // Use Cramer's rule solver which requires non-singular Gram matrix.
  assert detG != 0.0;
  coefficients := SolveLinearSystemCramer(G, g);
}

// </vc-code>
