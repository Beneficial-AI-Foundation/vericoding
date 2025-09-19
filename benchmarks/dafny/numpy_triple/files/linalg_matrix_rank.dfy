// <vc-preamble>
// Helper predicate to check if a matrix is zero
ghost predicate IsZeroMatrix(A: seq<seq<real>>)
  requires |A| > 0
  requires forall i :: 0 <= i < |A| ==> |A[i]| == |A[0]|
{
  forall i, j :: 0 <= i < |A| && 0 <= j < |A[i]| ==> A[i][j] == 0.0
}

// Helper predicate to check if a matrix is identity
ghost predicate IsIdentityMatrix(A: seq<seq<real>>)
  requires |A| > 0
  requires forall i :: 0 <= i < |A| ==> |A[i]| == |A[0]|
  requires |A| == |A[0]|  // Square matrix
{
  forall i, j :: 0 <= i < |A| && 0 <= j < |A[i]| ==> 
    A[i][j] == (if i == j then 1.0 else 0.0)
}

// Helper predicate to check if a row is all zeros
ghost predicate HasZeroRow(A: seq<seq<real>>)
  requires |A| > 0
  requires forall i :: 0 <= i < |A| ==> |A[i]| == |A[0]|
{
  exists i :: 0 <= i < |A| && 
    forall j :: 0 <= j < |A[i]| ==> A[i][j] == 0.0
}

// Helper predicate to check if a column is all zeros
ghost predicate HasZeroColumn(A: seq<seq<real>>)
  requires |A| > 0
  requires forall i :: 0 <= i < |A| ==> |A[i]| == |A[0]|
{
  exists j {:trigger A[0][j]} :: 0 <= j < |A[0]| && 
    forall i {:trigger A[i][j]} :: 0 <= i < |A| ==> A[i][j] == 0.0
}

// Helper predicate to check if two rows are identical
ghost predicate HasIdenticalRows(A: seq<seq<real>>)
  requires |A| > 0
  requires forall i :: 0 <= i < |A| ==> |A[i]| == |A[0]|
{
  exists i1, i2 :: 0 <= i1 < |A| && 0 <= i2 < |A| && i1 != i2 &&
    forall j :: 0 <= j < |A[i1]| ==> A[i1][j] == A[i2][j]
}

// Helper predicate to check if two columns are identical  
ghost predicate HasIdenticalColumns(A: seq<seq<real>>)
  requires |A| > 0
  requires forall i :: 0 <= i < |A| ==> |A[i]| == |A[0]|
{
  exists j1, j2 {:trigger A[0][j1], A[0][j2]} :: 0 <= j1 < |A[0]| && 0 <= j2 < |A[0]| && j1 != j2 &&
    forall i {:trigger A[i][j1], A[i][j2]} :: 0 <= i < |A| ==> A[i][j1] == A[i][j2]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method MatrixRank(A: seq<seq<real>>) returns (rank: nat)
  // Matrix must be non-empty and well-formed
  requires |A| > 0
  requires |A[0]| > 0
  requires forall i :: 0 <= i < |A| ==> |A[i]| == |A[0]|
  
  // Basic bounds: rank is bounded by matrix dimensions
  ensures rank <= (if |A| < |A[0]| then |A| else |A[0]|)
  
  // Zero matrix has rank 0
  ensures IsZeroMatrix(A) ==> rank == 0
  
  // Identity matrix has full rank (for square matrices)
  ensures |A| == |A[0]| ==> IsIdentityMatrix(A) ==> rank == |A|
  
  // If any row is all zeros, rank is less than number of rows
  ensures HasZeroRow(A) ==> rank < |A|
  
  // If any column is all zeros, rank is less than number of columns
  ensures HasZeroColumn(A) ==> rank < |A[0]|
  
  // If two rows are identical, rank is less than number of rows (when m > 1)
  ensures |A| > 1 ==> HasIdenticalRows(A) ==> rank < |A|
  
  // If two columns are identical, rank is less than number of columns (when n > 1)  
  ensures |A[0]| > 1 ==> HasIdenticalColumns(A) ==> rank < |A[0]|
  
  // For 1×1 matrices, rank is 1 if non-zero, 0 if zero
  ensures |A| == 1 && |A[0]| == 1 ==> 
    (rank == 1 <==> A[0][0] != 0.0) && (rank == 0 <==> A[0][0] == 0.0)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
