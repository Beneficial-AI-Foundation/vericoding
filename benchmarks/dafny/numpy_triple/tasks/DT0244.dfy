// <vc-preamble>
/*
 * SVD Values Computation
 * 
 * Computes the singular values of a matrix without computing the U and V matrices.
 * The singular values are the square roots of the eigenvalues of A^T @ A (or A @ A^T),
 * returned in descending order.
 */

// Matrix represented as sequence of rows, each row is a sequence of reals
type Matrix = seq<seq<real>>
type Vector = seq<real>

// Helper function to compute the minimum of two natural numbers
function Min(a: nat, b: nat): nat
{
    if a <= b then a else b
}

// Helper function to compute Frobenius norm squared of a matrix
function FrobeniusNormSquared(x: Matrix): real
    requires forall i :: 0 <= i < |x| ==> |x[i]| == |x[0]|  // All rows same length
{
    if |x| == 0 then 0.0
    else
        var sum := 0.0;
        sum + SumOfSquaresAllElements(x, 0)
}

// Recursive helper for computing sum of squares of all elements
function SumOfSquaresAllElements(x: Matrix, row: nat): real
    requires forall i :: 0 <= i < |x| ==> |x[i]| == |x[0]|  // All rows same length
    requires row <= |x|
    decreases |x| - row
{
    if row >= |x| then 0.0
    else SumOfSquaresRow(x[row], 0) + SumOfSquaresAllElements(x, row + 1)
}

// Helper to compute sum of squares in a row
function SumOfSquaresRow(row: seq<real>, col: nat): real
    requires col <= |row|
    decreases |row| - col
{
    if col >= |row| then 0.0
    else row[col] * row[col] + SumOfSquaresRow(row, col + 1)
}

// Check if matrix is zero matrix
predicate IsZeroMatrix(x: Matrix)
    requires forall i :: 0 <= i < |x| ==> |x[i]| == |x[0]|  // All rows same length
{
    forall i, j :: 0 <= i < |x| && 0 <= j < |x[i]| ==> x[i][j] == 0.0
}

// Check if vector is sorted in descending order
predicate IsSortedDescending(v: Vector)
{
    forall i, j :: 0 <= i <= j < |v| ==> v[i] >= v[j]
}

// Check if all elements in vector are non-negative
predicate AllNonNegative(v: Vector)
{
    forall i :: 0 <= i < |v| ==> v[i] >= 0.0
}

// Compute sum of squares of vector elements
function SumOfSquares(v: Vector): real
{
    if |v| == 0 then 0.0
    else SumOfSquaresHelper(v, 0)
}

function SumOfSquaresHelper(v: Vector, index: nat): real
    requires index <= |v|
    decreases |v| - index
{
    if index >= |v| then 0.0
    else v[index] * v[index] + SumOfSquaresHelper(v, index + 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SvdVals(x: Matrix) returns (result: Vector)
    // Well-formed matrix preconditions
    requires |x| > 0 ==> forall i :: 0 <= i < |x| ==> |x[i]| == |x[0]|  // All rows same length
    
    // Postconditions capturing the mathematical properties of singular values
    ensures |result| == (if |x| == 0 then 0 else Min(|x|, |x[0]|))
    
    // Property 1: All singular values are non-negative
    ensures AllNonNegative(result)
    
    // Property 2: Singular values are sorted in descending order
    ensures IsSortedDescending(result)
    
    // Property 3: Each singular value is bounded by the Frobenius norm
    ensures |x| > 0 ==> forall i :: 0 <= i < |result| ==> 
        result[i] * result[i] <= FrobeniusNormSquared(x)
    
    // Property 4: If the matrix is zero, all singular values are zero
    ensures |x| > 0 && IsZeroMatrix(x) ==> 
        forall i :: 0 <= i < |result| ==> result[i] == 0.0
    
    // Property 5: Sum of squares of singular values equals Frobenius norm squared
    // (This is an equality for exact SVD, but we use <= for numerical stability)
    ensures |x| > 0 ==> SumOfSquares(result) <= FrobeniusNormSquared(x)
    
    // Property 6: For non-zero matrices, at least one singular value is positive
    ensures |x| > 0 && !IsZeroMatrix(x) ==> 
        exists i :: 0 <= i < |result| && result[i] > 0.0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
