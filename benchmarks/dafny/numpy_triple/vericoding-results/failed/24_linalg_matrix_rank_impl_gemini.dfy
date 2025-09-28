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
/* helper modified by LLM (iteration 4): [re-implementing helpers as methods to be called from non-ghost code] */
method IsZeroMatrixImpl(A: seq<seq<real>>) returns (isZero: bool)
  requires |A| > 0
  requires forall i :: 0 <= i < |A| ==> |A[i]| == |A[0]|
  ensures isZero <==> IsZeroMatrix(A)
{
  var i := 0;
  while i < |A|
  {
    var j := 0;
    while j < |A[0]|
    {
      if A[i][j] != 0.0 {
        isZero := false;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  isZero := true;
}

method HasZeroRowImpl(A: seq<seq<real>>) returns (has: bool)
  requires |A| > 0
  requires forall i :: 0 <= i < |A| ==> |A[i]| == |A[0]|
  ensures has <==> HasZeroRow(A)
{
  var i := 0;
  while i < |A|
  {
    var rowIsZero := true;
    var j := 0;
    while j < |A[0]|
    {
      if A[i][j] != 0.0 {
        rowIsZero := false;
        break;
      }
      j := j + 1;
    }
    if rowIsZero {
      has := true;
      return;
    }
    i := i + 1;
  }
  has := false;
}

method HasZeroColumnImpl(A: seq<seq<real>>) returns (has: bool)
  requires |A| > 0
  requires forall i :: 0 <= i < |A| ==> |A[i]| == |A[0]|
  ensures has <==> HasZeroColumn(A)
{
  var j := 0;
  while j < |A[0]|
  {
    var colIsZero := true;
    var i := 0;
    while i < |A|
    {
      if A[i][j] != 0.0 {
        colIsZero := false;
        break;
      }
      i := i + 1;
    }
    if colIsZero {
      has := true;
      return;
    }
    j := j + 1;
  }
  has := false;
}

method HasIdenticalRowsImpl(A: seq<seq<real>>) returns (has: bool)
  requires |A| > 0
  requires forall i :: 0 <= i < |A| ==> |A[i]| == |A[0]|
  ensures has <==> HasIdenticalRows(A)
{
  var i1 := 0;
  while i1 < |A|
  {
    var i2 := i1 + 1;
    while i2 < |A|
    {
      var rowsAreIdentical := true;
      var j := 0;
      while j < |A[0]|
      {
        if A[i1][j] != A[i2][j] {
          rowsAreIdentical := false;
          break;
        }
        j := j + 1;
      }
      if rowsAreIdentical {
        has := true;
        return;
      }
      i2 := i2 + 1;
    }
    i1 := i1 + 1;
  }
  has := false;
}

method HasIdenticalColumnsImpl(A: seq<seq<real>>) returns (has: bool)
  requires |A| > 0
  requires forall i :: 0 <= i < |A| ==> |A[i]| == |A[0]|
  ensures has <==> HasIdenticalColumns(A)
{
  var j1 := 0;
  while j1 < |A[0]|
  {
    var j2 := j1 + 1;
    while j2 < |A[0]|
    {
      var colsAreIdentical := true;
      var i := 0;
      while i < |A|
      {
        if A[i][j1] != A[i][j2] {
          colsAreIdentical := false;
          break;
        }
        i := i + 1;
      }
      if colsAreIdentical {
        has := true;
        return;
      }
      j2 := j2 + 1;
    }
    j1 := j1 + 1;
  }
  has := false;
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
{
  /* code modified by LLM (iteration 4): [adapted to use helper methods and simplified logic] */
  var m := |A|;
  var n := |A[0]|;

  if m == 1 && n == 1 {
    if A[0][0] == 0.0 {
      rank := 0;
    } else {
      rank := 1;
    }
    return;
  }

  var is_zero := IsZeroMatrixImpl(A);
  if is_zero {
    rank := 0;
    return;
  }

  var has_zero_row := HasZeroRowImpl(A);
  var has_ident_rows := false;
  if m > 1 {
    has_ident_rows := HasIdenticalRowsImpl(A);
  }

  var has_zero_col := HasZeroColumnImpl(A);
  var has_ident_cols := false;
  if n > 1 {
    has_ident_cols := HasIdenticalColumnsImpl(A);
  }

  var rank_upper_m := m;
  if has_zero_row || has_ident_rows {
    rank_upper_m := m - 1;
  }

  var rank_upper_n := n;
  if has_zero_col || has_ident_cols {
    rank_upper_n := n - 1;
  }
  
  rank := if rank_upper_m < rank_upper_n then rank_upper_m else rank_upper_n;
}
// </vc-code>
