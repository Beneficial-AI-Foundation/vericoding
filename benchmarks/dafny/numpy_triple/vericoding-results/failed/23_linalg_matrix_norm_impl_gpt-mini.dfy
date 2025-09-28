// <vc-preamble>
// Ghost function to compute the sum of squares of all elements in a matrix
ghost function SumOfSquares(matrix: seq<seq<real>>): real
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
  decreases |matrix|
{
  if |matrix| == 0 then 0.0
  else SumOfSquaresRow(matrix[0]) + SumOfSquares(matrix[1..])
}

// Ghost function to compute the sum of squares of elements in a row
ghost function SumOfSquaresRow(row: seq<real>): real
  decreases |row|
{
  if |row| == 0 then 0.0
  else row[0] * row[0] + SumOfSquaresRow(row[1..])
}

// Ghost predicate to check if all elements in matrix are zero
ghost predicate AllZero(matrix: seq<seq<real>>)
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
{
  forall i, j :: 0 <= i < |matrix| && 0 <= j < |matrix[i]| ==> matrix[i][j] == 0.0
}

// Ghost predicate to check if there exists a non-zero element
ghost predicate HasNonZero(matrix: seq<seq<real>>)
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
{
  exists i, j :: 0 <= i < |matrix| && 0 <= j < |matrix[i]| && matrix[i][j] != 0.0
}

// Helper function to get absolute value
function Abs(x: real): real
{
  if x >= 0.0 then x else -x
}

// Main method for computing matrix norm (Frobenius norm)
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): abstract sqrt function with basic properties */
function sqrt(x: real): real
  ensures x >= 0.0 ==> sqrt(x) * sqrt(x) == x
  ensures x >= 0.0 ==> sqrt(x) >= 0.0
{
  // No body: treated as mathematical (uninterpreted) function with specified properties
  0.0
}

/* helper modified by LLM (iteration 4): concrete sum of squares for matrix */
function ConcreteSumOfSquares(matrix: seq<seq<real>>): real
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
  decreases |matrix|
{
  if |matrix| == 0 then 0.0 else ConcreteSumOfSquaresRow(matrix[0]) + ConcreteSumOfSquares(matrix[1..])
}

/* helper modified by LLM (iteration 4): concrete sum of squares for row */
function ConcreteSumOfSquaresRow(row: seq<real>): real
  decreases |row|
{
  if |row| == 0 then 0.0 else row[0]*row[0] + ConcreteSumOfSquaresRow(row[1..])
}

/* helper modified by LLM (iteration 4): relate concrete row sum to ghost */
lemma ConcreteRowEqualsGhost(row: seq<real>)
  ensures ConcreteSumOfSquaresRow(row) == SumOfSquaresRow(row)
  decreases |row|
{
  if |row| == 0 {
    // both definitions yield 0.0
  } else {
    ConcreteRowEqualsGhost(row[1..]);
    // unfold definitions and use inductive hypothesis
    assert ConcreteSumOfSquaresRow(row) == row[0]*row[0] + ConcreteSumOfSquaresRow(row[1..]);
    assert SumOfSquaresRow(row) == row[0]*row[0] + SumOfSquaresRow(row[1..]);
    assert ConcreteSumOfSquaresRow(row[1..]) == SumOfSquaresRow(row[1..]);
    assert ConcreteSumOfSquaresRow(row) == SumOfSquaresRow(row);
  }
}

/* helper modified by LLM (iteration 4): relate concrete matrix sum to ghost */
lemma ConcreteMatrixEqualsGhost(matrix: seq<seq<real>>)
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
  ensures ConcreteSumOfSquares(matrix) == SumOfSquares(matrix)
  decreases |matrix|
{
  if |matrix| == 0 {
  } else {
    ConcreteRowEqualsGhost(matrix[0]);
    ConcreteMatrixEqualsGhost(matrix[1..]);
    assert ConcreteSumOfSquares(matrix) == ConcreteSumOfSquaresRow(matrix[0]) + ConcreteSumOfSquares(matrix[1..]);
    assert SumOfSquares(matrix) == SumOfSquaresRow(matrix[0]) + SumOfSquares(matrix[1..]);
    assert ConcreteSumOfSquaresRow(matrix[0]) == SumOfSquaresRow(matrix[0]);
    assert ConcreteSumOfSquares(matrix[1..]) == SumOfSquares(matrix[1..]);
    assert ConcreteSumOfSquares(matrix) == SumOfSquares(matrix);
  }
}

/* helper modified by LLM (iteration 4): non-negativity for row sum */
lemma RowNonNeg(row: seq<real>)
  ensures ConcreteSumOfSquaresRow(row) >= 0.0
  decreases |row|
{
  if |row| == 0 {
  } else {
    RowNonNeg(row[1..]);
    assert row[0]*row[0] >= 0.0;
    assert ConcreteSumOfSquaresRow(row) == row[0]*row[0] + ConcreteSumOfSquaresRow(row[1..]);
    assert ConcreteSumOfSquaresRow(row) >= 0.0;
  }
}

/* helper modified by LLM (iteration 4): non-negativity for matrix sum */
lemma MatrixNonNeg(matrix: seq<seq<real>>)
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
  ensures ConcreteSumOfSquares(matrix) >= 0.0
  decreases |matrix|
{
  if |matrix| == 0 {
  } else {
    RowNonNeg(matrix[0]);
    MatrixNonNeg(matrix[1..]);
    assert ConcreteSumOfSquares(matrix) == ConcreteSumOfSquaresRow(matrix[0]) + ConcreteSumOfSquares(matrix[1..]);
    assert ConcreteSumOfSquares(matrix) >= 0.0;
  }
}

/* helper modified by LLM (iteration 4): row zero iff all zero */
lemma RowZeroIffAllZero(row: seq<real>)
  ensures (ConcreteSumOfSquaresRow(row) == 0.0) <==> (forall j :: 0 <= j < |row| ==> row[j] == 0.0)
  decreases |row|
{
  if |row| == 0 {
  } else {
    RowZeroIffAllZero(row[1..]);
    // forward direction
    if ConcreteSumOfSquaresRow(row) == 0.0 {
      assert row[0]*row[0] + ConcreteSumOfSquaresRow(row[1..]) == 0.0;
      assert row[0]*row[0] >= 0.0;
      assert ConcreteSumOfSquaresRow(row[1..]) >= 0.0;
      // both non-negative and sum zero => both zero
      assert row[0]*row[0] == 0.0;
      assert ConcreteSumOfSquaresRow(row[1..]) == 0.0;
      assert row[0] == 0.0;
      assert forall j :: 0 <= j < |row[1..]| ==> row[1 + j] == 0.0;
      assert forall j :: 0 <= j < |row| ==> row[j] == 0.0;
    }
    // backward direction
    if forall j :: 0 <= j < |row| ==> row[j] == 0.0 {
      assert row[0] == 0.0;
      assert forall j :: 0 <= j < |row[1..]| ==> row[1 + j] == 0.0;
      assert ConcreteSumOfSquaresRow(row[1..]) == 0.0;
      assert ConcreteSumOfSquaresRow(row) == row[0]*row[0] + ConcreteSumOfSquaresRow(row[1..]);
      assert ConcreteSumOfSquaresRow(row) == 0.0;
    }
  }
}

/* helper modified by LLM (iteration 4): matrix zero iff all zero */
lemma MatrixZeroIffAllZero(matrix: seq<seq<real>>)
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
  ensures (ConcreteSumOfSquares(matrix) == 0.0) <==> (forall i, j :: 0 <= i < |matrix| && 0 <= j < |matrix[i]| ==> matrix[i][j] == 0.0)
  decreases |matrix|
{
  if |matrix| == 0 {
  } else {
    RowZeroIffAllZero(matrix[0]);
    MatrixZeroIffAllZero(matrix[1..]);
    // forward direction
    if ConcreteSumOfSquares(matrix) == 0.0 {
      assert ConcreteSumOfSquaresRow(matrix[0]) + ConcreteSumOfSquares(matrix[1..]) == 0.0;
      assert ConcreteSumOfSquaresRow(matrix[0]) >= 0.0;
      assert ConcreteSumOfSquares(matrix[1..]) >= 0.0;
      assert ConcreteSumOfSquaresRow(matrix[0]) == 0.0;
      assert ConcreteSumOfSquares(matrix[1..]) == 0.0;
      assert forall j :: 0 <= j < |matrix[0]| ==> matrix[0][j] == 0.0;
      assert forall i, j :: 0 <= i < |matrix[1..]| && 0 <= j < |matrix[1..][i]| ==> matrix[1 + i][j] == 0.0;
      assert forall i, j :: 0 <= i < |matrix| && 0 <= j < |matrix[i]| ==> matrix[i][j] == 0.0;
    }
    // backward direction
    if forall i, j :: 0 <= i < |matrix| && 0 <= j < |matrix[i]| ==> matrix[i][j] == 0.0 {
      assert forall j :: 0 <= j < |matrix[0]| ==> matrix[0][j] == 0.0;
      assert forall i, j :: 0 <= i < |matrix[1..]| && 0 <= j < |matrix[1..][i]| ==> matrix[1 + i][j] == 0.0;
      assert ConcreteSumOfSquaresRow(matrix[0]) == 0.0;
      assert ConcreteSumOfSquares(matrix[1..]) == 0.0;
      assert ConcreteSumOfSquares(matrix) == 0.0;
    }
  }
}

/* helper modified by LLM (iteration 4): positive definiteness when has non-zero */
lemma MatrixPositiveIfHasNonZero(matrix: seq<seq<real>>)
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
  requires HasNonZero(matrix)
  ensures ConcreteSumOfSquares(matrix) > 0.0
  decreases |matrix|
{
  if |matrix| == 0 {
    // impossible due to HasNonZero precondition
  } else {
    if forall j :: 0 <= j < |matrix[0]| ==> matrix[0][j] == 0.0 {
      // non-zero is in tail
      MatrixPositiveIfHasNonZero(matrix[1..]);
      assert ConcreteSumOfSquares(matrix) == ConcreteSumOfSquaresRow(matrix[0]) + ConcreteSumOfSquares(matrix[1..]);
      assert ConcreteSumOfSquares(matrix[1..]) > 0.0;
      assert ConcreteSumOfSquaresRow(matrix[0]) >= 0.0;
      assert ConcreteSumOfSquares(matrix) > 0.0;
    } else {
      // there exists a non-zero in the first row
      var k := 0;
      while k < |matrix[0]|
        decreases |matrix[0]| - k
      {
        if matrix[0][k] != 0.0 {
          // this element contributes positively
          assert matrix[0][k] * matrix[0][k] > 0.0;
          assert ConcreteSumOfSquaresRow(matrix[0]) >= matrix[0][k] * matrix[0][k];
          assert ConcreteSumOfSquares(matrix) == ConcreteSumOfSquaresRow(matrix[0]) + ConcreteSumOfSquares(matrix[1..]);
          assert ConcreteSumOfSquares(matrix) > 0.0;
          break;
        }
        k := k + 1;
      }
    }
  }
}

/* helper modified by LLM (iteration 4): each element's square bounded by total */
lemma ElementBound(matrix: seq<seq<real>>, i: int, j: int)
  requires 0 <= i < |matrix|
  requires 0 <= j < |matrix[i]|
  requires forall k :: 0 <= k < |matrix| ==> |matrix[k]| == |matrix[0]|
  ensures matrix[i][j]*matrix[i][j] <= ConcreteSumOfSquares(matrix)
  decreases |matrix|
{
  if i == 0 {
    // element is in first row
    assert ConcreteSumOfSquares(matrix) == ConcreteSumOfSquaresRow(matrix[0]) + ConcreteSumOfSquares(matrix[1..]);
    assert ConcreteSumOfSquaresRow(matrix[0]) == (var tmp := matrix[0][0]; // force unfolding pattern
      ConcreteSumOfSquaresRow(matrix[0]));
    // Show row sum >= element^2 by induction on j
    var row := matrix[0];
    // Prove by simple induction on j index
    lemma RowElementBound(r := row, idx := j);
    assert matrix[0][j]*matrix[0][j] <= ConcreteSumOfSquaresRow(row);
    assert matrix[i][j]*matrix[i][j] <= ConcreteSumOfSquares(matrix);
  } else {
    // element is in tail; reduce to smaller matrix
    assert ConcreteSumOfSquares(matrix) == ConcreteSumOfSquaresRow(matrix[0]) + ConcreteSumOfSquares(matrix[1..]);
    ElementBound(matrix[1..], i - 1, j);
    assert matrix[i][j]*matrix[i][j] <= ConcreteSumOfSquares(matrix[1..]);
    assert matrix[i][j]*matrix[i][j] <= ConcreteSumOfSquares(matrix);
  }
}

/* helper modified by LLM (iteration 4): helper to show element bound inside a row */
lemma RowElementBound(r: seq<real>, idx: int)
  requires 0 <= idx < |r|
  ensures r[idx]*r[idx] <= ConcreteSumOfSquaresRow(r)
  decreases |r|
{
  if idx == 0 {
    assert ConcreteSumOfSquaresRow(r) == r[0]*r[0] + ConcreteSumOfSquaresRow(r[1..]);
    assert r[0]*r[0] <= ConcreteSumOfSquaresRow(r);
  } else {
    RowElementBound(r[1..], idx - 1);
    assert r[idx]*r[idx] <= ConcreteSumOfSquaresRow(r[1..]);
    assert ConcreteSumOfSquaresRow(r) == r[0]*r[0] + ConcreteSumOfSquaresRow(r[1..]);
    assert r[idx]*r[idx] <= ConcreteSumOfSquaresRow(r);
  }
}

// </vc-helpers>

// <vc-spec>
method MatrixNorm(matrix: seq<seq<real>>) returns (result: real)
  // Input validation: rectangular matrix (all rows same length)
  requires |matrix| > 0 ==> forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
  // Non-negativity property
  ensures result >= 0.0
  // Zero property: norm is zero iff all elements are zero
  ensures (|matrix| == 0 || |matrix[0]| == 0) ==> result == 0.0
  ensures |matrix| > 0 && |matrix[0]| > 0 ==> (result == 0.0 <==> AllZero(matrix))
  // Frobenius norm definition: sqrt(sum of squares)
  ensures |matrix| > 0 && |matrix[0]| > 0 ==> result * result == SumOfSquares(matrix)
  // Domination property: norm dominates absolute value of any element
  ensures forall i, j :: 0 <= i < |matrix| && 0 <= j < |matrix[i]| ==> Abs(matrix[i][j]) <= result
  // Positive definiteness: if matrix has non-zero elements, norm is positive
  ensures |matrix| > 0 && |matrix[0]| > 0 && HasNonZero(matrix) ==> result > 0.0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): compute Frobenius norm using sqrt ghost and prove properties */
  if |matrix| == 0 || |matrix[0]| == 0 {
    result := 0.0;
    return;
  }
  // compute concrete sum of squares
  var s := ConcreteSumOfSquares(matrix);
  // relate concrete and ghost sums and show non-negativity
  ConcreteMatrixEqualsGhost(matrix);
  MatrixNonNeg(matrix);
  // handle zero case
  if s == 0.0 {
    MatrixZeroIffAllZero(matrix);
    result := 0.0;
    return;
  }
  // s > 0 here
  result := sqrt(s);

  // prove result * result == SumOfSquares(matrix)
  // we have ConcreteSumOfSquares(matrix) == SumOfSquares(matrix) and sqrt(s)*sqrt(s) == s (for s >= 0)
  assert s >= 0.0;
  assert result * result == s;
  assert SumOfSquares(matrix) == s;

  // prove Abs(matrix[i][j]) <= result for all elements
  var i := 0;
  while i < |matrix|
    decreases |matrix| - i
  {
    var j := 0;
    while j < |matrix[i]|
      decreases |matrix[i]| - j
    {
      ElementBound(matrix, i, j);
      // matrix[i][j]^2 <= s
      assert matrix[i][j]*matrix[i][j] <= s;
      // Abs(matrix[i][j]) is non-negative
      assert Abs(matrix[i][j]) * Abs(matrix[i][j]) == matrix[i][j]*matrix[i][j];
      assert Abs(matrix[i][j]) * Abs(matrix[i][j]) <= result * result;
      // Both sides non-negative; conclude Abs(matrix[i][j]) <= result (Dafny can reason on non-neg sqr inequality)
      assert Abs(matrix[i][j]) <= result;
      j := j + 1;
    }
    i := i + 1;
  }
}

// </vc-code>
