// <vc-preamble>
/*
 * Covariance matrix computation specification.
 * 
 * Estimates a covariance matrix from data where each row represents a variable
 * and each column represents an observation. Returns a symmetric positive 
 * semi-definite covariance matrix following the mathematical definition:
 * Cov(X_i, X_j) = E[(X_i - μ_i)(X_j - μ_j)]
 */

// Helper function to compute the mean of a sequence
function Mean(data: seq<real>): real
    requires |data| > 0
{
    Sum(data) / (|data| as real)
}

// Helper function to sum elements in a sequence  
function Sum(data: seq<real>): real
{
    if |data| == 0 then 0.0
    else data[0] + Sum(data[1..])
}

// Helper function to compute covariance between two variables
function Covariance(var_i: seq<real>, var_j: seq<real>): real
    requires |var_i| == |var_j| > 0
{
    if |var_i| == 1 then 0.0
    else
        var mean_i := Mean(var_i);
        var mean_j := Mean(var_j);
        var deviations := seq(|var_i|, k requires 0 <= k < |var_i| => (var_i[k] - mean_i) * (var_j[k] - mean_j));
        Sum(deviations) / ((|var_i| - 1) as real)
}

// Main method specification for numpy covariance matrix computation
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method NumpyCov(m: seq<seq<real>>) returns (cov_matrix: seq<seq<real>>)
    requires |m| > 0                              // At least one variable
    requires |m[0]| > 0                           // At least one observation
    requires forall i :: 0 <= i < |m| ==> |m[i]| == |m[0]|  // All variables have same number of observations
    
    ensures |cov_matrix| == |m|                   // Output is vars x vars matrix
    ensures forall i :: 0 <= i < |cov_matrix| ==> |cov_matrix[i]| == |m|
    
    // Symmetry property: C[i,j] = C[j,i]
    ensures forall i, j :: 0 <= i < |m| && 0 <= j < |m| ==> 
        cov_matrix[i][j] == cov_matrix[j][i]
    
    // Diagonal elements are non-negative (variances)
    ensures forall i :: 0 <= i < |m| ==> cov_matrix[i][i] >= 0.0
    
    // Covariance formula: each element C[i,j] equals the covariance of variables i and j
    ensures forall i, j :: 0 <= i < |m| && 0 <= j < |m| ==>
        cov_matrix[i][j] == Covariance(m[i], m[j])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
