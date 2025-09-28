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
// Helper predicate to validate matrix dimensions
predicate ValidMatrix(matrix: seq<seq<real>>)
{
    |matrix| > 0 && |matrix[0]| > 0 &&
    forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
}

// Helper lemma to prove symmetry of covariance
lemma CovarianceSymmetry(var_i: seq<real>, var_j: seq<real>)
    requires |var_i| == |var_j| > 0
    ensures Covariance(var_i, var_j) == Covariance(var_j, var_i)
{
    if |var_i| == 1 {
        // Base case: both return 0.0
    } else {
        var mean_i := Mean(var_i);
        var mean_j := Mean(var_j);
        var dev_ij := seq(|var_i|, k requires 0 <= k < |var_i| => (var_i[k] - mean_i) * (var_j[k] - mean_j));
        var dev_ji := seq(|var_j|, k requires 0 <= k < |var_j| => (var_j[k] - mean_j) * (var_i[k] - mean_i));
        
        // The deviation products are identical due to commutativity of multiplication
        assert forall k :: 0 <= k < |var_i| ==> dev_ij[k] == dev_ji[k];
        assert dev_ij == dev_ji;
    }
}

/* helper modified by LLM (iteration 3): fixed assertion by proving squares are non-negative step by step */
lemma VarianceNonNegative(var_i: seq<real>)
    requires |var_i| > 0
    ensures Covariance(var_i, var_i) >= 0.0
{
    if |var_i| == 1 {
        // Base case: returns 0.0 which is >= 0.0
    } else {
        var mean_i := Mean(var_i);
        var deviations := seq(|var_i|, k requires 0 <= k < |var_i| => (var_i[k] - mean_i) * (var_i[k] - mean_i));
        
        // Prove that each squared deviation is non-negative
        forall k | 0 <= k < |var_i|
            ensures deviations[k] >= 0.0
        {
            var diff := var_i[k] - mean_i;
            assert deviations[k] == diff * diff;
            SquareNonNegative(diff);
        }
        
        // Sum of non-negative numbers is non-negative
        SumNonNegative(deviations);
        assert Sum(deviations) >= 0.0;
        
        // Division by positive number preserves non-negativity
        assert ((|var_i| - 1) as real) > 0.0;
        assert Sum(deviations) / ((|var_i| - 1) as real) >= 0.0;
    }
}

lemma SquareNonNegative(x: real)
    ensures x * x >= 0.0
{
    // Mathematical fact: any real number squared is non-negative
}

lemma SumNonNegative(data: seq<real>)
    requires forall k :: 0 <= k < |data| ==> data[k] >= 0.0
    ensures Sum(data) >= 0.0
{
    if |data| == 0 {
        // Base case: Sum([]) = 0.0 >= 0.0
    } else {
        // Inductive case: data[0] >= 0.0 and Sum(data[1..]) >= 0.0
        SumNonNegative(data[1..]);
        assert data[0] >= 0.0;
        assert Sum(data[1..]) >= 0.0;
        assert Sum(data) == data[0] + Sum(data[1..]) >= 0.0;
    }
}
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
    /* code modified by LLM (iteration 3): simplified implementation without explicit assertions */
    var n := |m|;
    cov_matrix := seq(n, i requires 0 <= i < n => 
        seq(n, j requires 0 <= j < n => Covariance(m[i], m[j])));
    
    // Prove symmetry using the lemma
    forall i, j | 0 <= i < n && 0 <= j < n
        ensures cov_matrix[i][j] == cov_matrix[j][i]
    {
        CovarianceSymmetry(m[i], m[j]);
    }
    
    // Prove diagonal elements are non-negative
    forall i | 0 <= i < n
        ensures cov_matrix[i][i] >= 0.0
    {
        VarianceNonNegative(m[i]);
    }
}
// </vc-code>
