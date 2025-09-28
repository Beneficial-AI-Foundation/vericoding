// <vc-preamble>
// Matrix and vector type definitions
type Matrix = seq<seq<real>>
type Vector = seq<real>

// Predicate to check if a matrix is square with given dimension
predicate IsSquareMatrix(m: Matrix, n: nat)
{
  |m| == n && forall i :: 0 <= i < n ==> |m[i]| == n
}

// Predicate to check if a vector has given dimension
predicate IsVector(v: Vector, n: nat)
{
  |v| == n
}

// Matrix-vector multiplication: result[i] = sum(a[i][j] * v[j] for j in 0..n)
function MatrixVectorMultiply(a: Matrix, v: Vector, n: nat): Vector
  requires IsSquareMatrix(a, n) && IsVector(v, n)
  ensures IsVector(MatrixVectorMultiply(a, v, n), n)
{
  seq(n, i requires 0 <= i < n => 
    Sum(seq(n, j requires 0 <= j < n => a[i][j] * v[j])))
}

// Matrix multiplication: result[i][j] = sum(a[i][k] * b[k][j] for k in 0..n)
function MatrixMultiply(a: Matrix, b: Matrix, n: nat): Matrix
  requires IsSquareMatrix(a, n) && IsSquareMatrix(b, n)
  ensures IsSquareMatrix(MatrixMultiply(a, b, n), n)
{
  seq(n, i requires 0 <= i < n => 
    seq(n, j requires 0 <= j < n => 
      Sum(seq(n, k requires 0 <= k < n => a[i][k] * b[k][j]))))
}

// Identity matrix predicate
predicate IsIdentityMatrix(m: Matrix, n: nat)
  requires IsSquareMatrix(m, n)
{
  forall i, j :: 0 <= i < n && 0 <= j < n ==>
    m[i][j] == (if i == j then 1.0 else 0.0)
}

// Predicate to check if two matrices are inverses of each other
predicate AreInverses(a: Matrix, a_inv: Matrix, n: nat)
  requires IsSquareMatrix(a, n) && IsSquareMatrix(a_inv, n)
{
  IsIdentityMatrix(MatrixMultiply(a, a_inv, n), n) &&
  IsIdentityMatrix(MatrixMultiply(a_inv, a, n), n)
}

// Helper function to sum a sequence of reals
function Sum(s: seq<real>): real
{
  if |s| == 0 then 0.0
  else s[0] + Sum(s[1..])
}

// Main tensorsolve method specification
// </vc-preamble>

// <vc-helpers>
lemma SumOfZeros(s: seq<real>)
  requires forall i :: 0 <= i < |s| ==> s[i] == 0.0
  ensures Sum(s) == 0.0
  decreases |s|
{
  if |s| > 0 {
    SumOfZeros(s[1..]);
  }
}

lemma SumWithOneNonZero(s: seq<real>, k: nat)
  requires 0 <= k < |s|
  requires forall i :: 0 <= i < |s| && i != k ==> s[i] == 0.0
  ensures Sum(s) == s[k]
  decreases |s|
{
  if |s| == 1 {
  } else if k == 0 {
    var s_rest := s[1..];
    assert forall i :: 0 <= i < |s_rest| ==> s_rest[i] == 0.0;
    SumOfZeros(s_rest);
  } else {
    SumWithOneNonZero(s[1..], k - 1);
  }
}

lemma SumAddition(s1: seq<real>, s2: seq<real>)
  requires |s1| == |s2|
  ensures Sum(seq(|s1|, i => s1[i] + s2[i])) == Sum(s1) + Sum(s2)
  decreases |s1|
{
  if |s1| > 0 {
    SumAddition(s1[1..], s2[1..]);
  }
}

lemma SumScalarMultiplication(c: real, s: seq<real>)
  ensures Sum(seq(|s|, i => c * s[i])) == c * Sum(s)
  decreases |s|
{
  if |s| > 0 {
    SumScalarMultiplication(c, s[1..]);
  }
}

/* helper modified by LLM (iteration 2): fixed syntax error in assert statement */
lemma SummationSwap(n: nat, m: nat, f: (nat, nat) -> real)
  ensures Sum(seq(n, i => Sum(seq(m, j => f(i, j))))) == Sum(seq(m, j => Sum(seq(n, i => f(i, j)))))
  decreases n
{
  if n > 0 {
    var n_minus_1 := n - 1;
    SummationSwap(n_minus_1, m, f);
    var inner_sum_n := seq(m, j => f(n_minus_1, j));
    var sum_over_i_n_minus_1 := seq(m, j => Sum(seq(n_minus_1, i => f(i, j))));
    var sum_over_i_n := seq(m, j => Sum(seq(n, i => f(i, j))));
    assert forall j :: 0 <= j < m ==> sum_over_i_n[j] == sum_over_i_n_minus_1[j] + inner_sum_n[j];
    SumAddition(sum_over_i_n_minus_1, inner_sum_n);
  }
}

lemma IdentityMatrixVectorMultiplication(v: Vector, n: nat)
  requires IsVector(v, n)
  ensures forall I :: IsSquareMatrix(I, n) && IsIdentityMatrix(I, n) ==> MatrixVectorMultiply(I, v, n) == v
{
  if n > 0 {
    forall I | IsSquareMatrix(I, n) && IsIdentityMatrix(I, n)
      ensures MatrixVectorMultiply(I, v, n) == v
    {
      forall i | 0 <= i < n
        ensures (MatrixVectorMultiply(I, v, n))[i] == v[i]
      {
        var row_times_v := seq(n, j => I[i][j] * v[j]);
        assert forall j :: 0 <= j < n && j != i ==> row_times_v[j] == 0.0;
        assert row_times_v[i] == v[i];
        SumWithOneNonZero(row_times_v, i);
        assert Sum(row_times_v) == v[i];
      }
    }
  }
}

lemma MatrixVectorMultiplicationAssociativity(m1: Matrix, m2: Matrix, v: Vector, n: nat)
  requires IsSquareMatrix(m1, n) && IsSquareMatrix(m2, n) && IsVector(v, n)
  ensures MatrixVectorMultiply(m1, MatrixVectorMultiply(m2, v, n), n) == MatrixVectorMultiply(MatrixMultiply(m1, m2, n), v, n)
{
  if n > 0 {
    forall i | 0 <= i < n
      ensures (MatrixVectorMultiply(m1, MatrixVectorMultiply(m2, v, n), n))[i] == (MatrixVectorMultiply(MatrixMultiply(m1, m2, n), v, n))[i]
    {
      calc {
        (MatrixVectorMultiply(m1, MatrixVectorMultiply(m2, v, n), n))[i];
      ==
        Sum(seq(n, k => m1[i][k] * Sum(seq(n, j => m2[k][j] * v[j]))));
      == { forall k | 0 <= k < n { SumScalarMultiplication(m1[i][k], seq(n, j => m2[k][j] * v[j])); } }
        Sum(seq(n, k => Sum(seq(n, j => m1[i][k] * m2[k][j] * v[j]))));
      == { SummationSwap(n, n, (k,j) => m1[i][k] * m2[k][j] * v[j]); }
        Sum(seq(n, j => Sum(seq(n, k => m1[i][k] * m2[k][j] * v[j]))));
      == { forall j | 0 <= j < n { SumScalarMultiplication(v[j], seq(n, k => m1[i][k] * m2[k][j])); } }
        Sum(seq(n, j => Sum(seq(n, k => m1[i][k] * m2[k][j])) * v[j]));
      ==
        Sum(seq(n, j => (MatrixMultiply(m1, m2, n))[i][j] * v[j]));
      ==
        (MatrixVectorMultiply(MatrixMultiply(m1, m2, n), v, n))[i];
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method tensorsolve(a: Matrix, b: Vector, n: nat) returns (x: Vector)
  requires IsSquareMatrix(a, n)
  requires IsVector(b, n)
  // Matrix a must be invertible
  requires exists a_inv :: IsSquareMatrix(a_inv, n) && AreInverses(a, a_inv, n)
  ensures IsVector(x, n)
  // Correctness: The solution satisfies a * x = b
  ensures MatrixVectorMultiply(a, x, n) == b
  // Uniqueness: x is the unique solution to a * x = b
  ensures forall y :: IsVector(y, n) && MatrixVectorMultiply(a, y, n) == b ==> y == x
  // The solution can be computed using the inverse: x = a_inv * b
  ensures exists a_inv :: IsSquareMatrix(a_inv, n) && AreInverses(a, a_inv, n) &&
            x == MatrixVectorMultiply(a_inv, b, n)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implemented logic to solve for x and prove postconditions */
  var a_inv :| IsSquareMatrix(a_inv, n) && AreInverses(a, a_inv, n);
  x := MatrixVectorMultiply(a_inv, b, n);

  MatrixVectorMultiplicationAssociativity(a, a_inv, b, n);
  IdentityMatrixVectorMultiplication(b, n);
  calc {
    MatrixVectorMultiply(a, x, n);
  ==
    MatrixVectorMultiply(a, MatrixVectorMultiply(a_inv, b, n), n);
  ==
    MatrixVectorMultiply(MatrixMultiply(a, a_inv, n), b, n);
  ==
    b;
  }
  assert MatrixVectorMultiply(a, x, n) == b;

  forall y | IsVector(y, n) && MatrixVectorMultiply(a, y, n) == b
    ensures y == x
  {
    MatrixVectorMultiplicationAssociativity(a_inv, a, y, n);
    IdentityMatrixVectorMultiplication(y, n);
    calc {
      y;
    ==
      MatrixVectorMultiply(MatrixMultiply(a_inv, a, n), y, n);
    ==
      MatrixVectorMultiply(a_inv, MatrixVectorMultiply(a, y, n), n);
    ==
      MatrixVectorMultiply(a_inv, b, n);
    ==
      x;
    }
  }
}
// </vc-code>
