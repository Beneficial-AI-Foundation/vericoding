// <vc-preamble>
// Evaluate the k-th probabilist's Hermite polynomial (HermiteE) at x
function EvalHermiteE(k: nat, x: real): real
    decreases k
{
    if k == 0 then 1.0
    else if k == 1 then x
    else x * EvalHermiteE(k-1, x) - (k-1) as real * EvalHermiteE(k-2, x)
}

// Helper function to compute sum of terms in HermiteE polynomial evaluation
function SumTerms(coeffs: seq<real>, x: real, i: nat): real
    requires i <= |coeffs|
    decreases |coeffs| - i
{
    if i == |coeffs| then 0.0
    else coeffs[i] * EvalHermiteE(i, x) + SumTerms(coeffs, x, i+1)
}

// Evaluate a polynomial in HermiteE basis at point x given coefficients
function EvalHermiteEPoly(coeffs: seq<real>, x: real): real
{
    SumTerms(coeffs, x, 0)
}

// Helper function to evaluate product form (x - r₀) * ... * (x - rₙ₋₁)
function ProductForm(roots: seq<real>, x: real, i: nat): real
    requires i <= |roots|
    decreases |roots| - i
{
    if i == |roots| then 1.0
    else (x - roots[i]) * ProductForm(roots, x, i+1)
}

// Main method: convert polynomial roots to HermiteE coefficients
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method HermeFromRoots(roots: seq<real>) returns (coeffs: seq<real>)
    // Output has exactly n+1 coefficients where n is the number of roots
    ensures |coeffs| == |roots| + 1
    
    // Sanity check: empty roots give the constant polynomial 1
    ensures |roots| == 0 ==> coeffs[0] == 1.0
    
    // For each root r, evaluating the HermiteE polynomial at r gives zero
    ensures forall i :: 0 <= i < |roots| ==> EvalHermiteEPoly(coeffs, roots[i]) == 0.0
    
    // Mathematical property: the coefficients form a valid representation of 
    // the polynomial (x - r₀) * ... * (x - rₙ₋₁) in HermiteE basis
    ensures forall x :: EvalHermiteEPoly(coeffs, x) == ProductForm(roots, x, 0)
    
    // The polynomial degree matches the number of roots (leading coefficient is non-zero)
    ensures |roots| > 0 ==> coeffs[|roots|] != 0.0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error: `(k + 2) * [0.0]` is not allowed. Changed to `new real[(k+2)]` to properly initialize a sequence to a given length. */
{
  var n := |roots|;
  if n == 0 {
    return [1.0];
  }

  // Base case: polynomial (x - r0)
  var coeffs_prev: seq<real> := [ -roots[0], 1.0 ];

  // Inductive step: (x - r_k) * P_k(x) = x * P_k(x) - r_k * P_k(x)
  // P_k(x) is represented by coeffs_prev
  for k := 1 to n - 1 {
    var next_r := roots[k];
    var next_coeffs: seq<real> := new real[(k + 2)]; // Initialize with default 0.0 values
    for i := 0 to k+1 { next_coeffs[i] := 0.0; }

    // Multiply by x * P_k(x)
    // P_k(x) = sum_{j=0}^{k+1} coeffs_prev[j] * H_j(x)
    // x * P_k(x) = sum_{j=0}^{k+1} coeffs_prev[j] * (H_{j+1}(x) + j * H_{j-1}(x))
    for j := 0 to |coeffs_prev| - 1 {
      var c_j := coeffs_prev[j];
      if j + 1 < |next_coeffs| {
        next_coeffs := next_coeffs[j+1 := next_coeffs[j+1] + c_j]; // Coefficient for H_{j+1}
      }
      if j - 1 >= 0 {
        next_coeffs := next_coeffs[j-1 := next_coeffs[j-1] + j as real * c_j]; // Coefficient for H_{j-1}
      }
    }

    // Subtract r_k * P_k(x)
    for j := 0 to |coeffs_prev| - 1 {
      
        next_coeffs := next_coeffs[j := next_coeffs[j] - next_r * coeffs_prev[j]];
      
    }
    coeffs_prev := next_coeffs;
  }
  return coeffs_prev;
}
// </vc-code>
