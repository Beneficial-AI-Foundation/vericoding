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
/* helper modified by LLM (iteration 5): fix swap to handle indices order */
method SwapRows(A: seq<seq<real>>, i: int, j: int) returns (A': seq<seq<real>>)
  requires 0 <= i < |A| && 0 <= j < |A|
  ensures |A'| == |A|
  ensures forall k :: 0 <= k < |A| ==> |A'[k]| == |A[k]|
  ensures forall k :: 0 <= k < |A| && k != i && k != j ==> A'[k] == A[k]
  ensures A'[i] == A[j]
  ensures A'[j] == A[i]
{
  if i == j {
    A' := A;
  } else {
    var minIdx := if i < j then i else j;
    var maxIdx := if i > j then i else j;
    A' := A[..minIdx] + [A[maxIdx]] + (if minIdx + 1 <= maxIdx then A[minIdx + 1..maxIdx] else []) + [A[minIdx]] + A[maxIdx + 1..];
  }
}

/* helper modified by LLM (iteration 5): maintained MakePivotOne */
method MakePivotOne(A: seq<seq<real>>, row: int, col: int) returns (A': seq<seq<real>>)
  requires 0 <= row < |A| && 0 <= col < |A[row]| && A[row][col] != 0.0
  ensures |A'| == |A|
  ensures forall k :: 0 <= k < |A| ==> |A'[k]| == |A[k]|
  ensures forall r, j :: 0 <= r < |A| && 0 <= j < |A[r]| && !(r == row) ==> A'[r][j] == A[r][j]
  ensures forall j :: 0 <= j < |A[row]| ==> A'[row][j] == A[row][j] / A[row][col]
{
  var newRow := seq(|A[row]|, j requires 0 <= j < |A[row]| => A[row][j] / A[row][col]);
  A' := A[..row] + [newRow] + A[row+1..];
}

/* helper modified by LLM (iteration 5): maintained EliminateBelow */
method EliminateBelow(A: seq<seq<real>>, pivotRow: int, col: int) returns (A': seq<seq<real>>)
  requires 0 <= pivotRow < |A| && 0 <= col < |A[pivotRow]| && A[pivotRow][col] != 0.0
  requires forall k :: 0 <= k < |A| ==> |A[k]| == |A[pivotRow]|
  ensures |A'| == |A|
  ensures forall k :: 0 <= k < |A| ==> |A'[k]| == |A[k]|
  ensures forall r, j :: 0 <= r < |A| && !(pivotRow < r && col <= j < |A[r]|) ==> A'[r][j] == A[r][j]
  ensures forall r :: pivotRow < r < |A| ==> A'[r][col] == 0.0
  ensures A'[pivotRow] == A[pivotRow]
{
  A' := A;
  var pivotVal := A[pivotRow][col];
  var t := pivotRow + 1;
  while t < |A|
  {
    var factor := A[t][col] / pivotVal;
    var newRow := seq(|A[t]|, j requires 0 <= j < |A[t]| => A[t][j] - factor * A[pivotRow][j]);
    A' := A'[..t] + [newRow] + A'[t+1..];
    t := t + 1;
  }
}

/* helper modified by LLM (iteration 5): maintained EliminateAbove */
method EliminateAbove(A: seq<seq<real>>, pivotRow: int, col: int) returns (A': seq<seq<real>>)
  requires 0 <= pivotRow < |A| && 0 <= col < |A[pivotRow]| && A[pivotRow][col] != 0.0
  requires forall k :: 0 <= k < |A| ==> |A[k]| == |A[pivotRow]|
  ensures |A'| == |A|
  ensures forall k :: 0 <= k < |A| ==> |A'[k]| == |A[k]|
  ensures forall r, j :: 0 <= r < |A| && !(0 <= r < pivotRow && col <= j < |A[r]|) ==> A'[r][j] == A[r][j]
  ensures forall r :: 0 <= r < pivotRow ==> A'[r][col] == 0.0
  ensures A'[pivotRow] == A[pivotRow]
{
  A' := A;
  var pivotVal := A[pivotRow][col];
  var t := 0;
  while t < pivotRow
  {
    var factor := A[t][col] / pivotVal;
    var newRow := seq(|A[t]|, j requires 0 <= j < |A[t]| => A[t][j] - factor * A[pivotRow][j]);
    A' := A'[..t] + [newRow] + A'[t+1..];
    t := t + 1;
  }
}

/* helper modified by LLM (iteration 5): fix FindNonZeroRow to use while true with if inside for safe indexing */
method FindNonZeroRow(A: seq<seq<real>>, startRow: int, col: int) returns (r: int)
  requires 0 <= startRow < |A| && 0 <= col < |A[startRow]|
  ensures -1 <= r < |A| && (r < 0 || (startRow <= r && A[r][col] != 0.0 && forall k :: startRow <= k < r ==> A[k][col] == 0.0))
  ensures r >= startRow || r == -1
{
  r := startRow;
  while true
    decreases |A| - r + 1
  {
    if r == |A| || A[r][col] != 0.0 {
      break;
    }
    r := r + 1;
  }
  if r == |A| {
    r := -1;
  }
}
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
/* code modified by LLM (iteration 5): added return statement */
{
  var A' := A;
  rank := 0;
  var col := 0;
  var row := 0;
  while row < |A| && col < |A[0]|
  {
    var pivotRow := FindNonZeroRow(A', row, col);
    if pivotRow != -1 {
      A' := SwapRows(A', row, pivotRow);
      A' := MakePivotOne(A', row, col);
      A' := EliminateBelow(A', row, col);
      A' := EliminateAbove(A', row, col);
      rank := rank + 1;
      row := row + 1;
    }
    col := col + 1;
  }
  return rank;
}
// </vc-code>
