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
/* helper modified by LLM (iteration 5): pointwise unfolding for MatrixVectorMultiply */
lemma MatrixVectorMultiplyIndex(a: Matrix, v: Vector, n: nat)
  requires IsSquareMatrix(a, n) && IsVector(v, n)
  ensures forall i :: 0 <= i < n ==> MatrixVectorMultiply(a, v, n)[i] == Sum(seq(n, j requires 0 <= j < n => a[i][j] * v[j]))
{
  // Unfold the function definition pointwise so the equality is available outside the forall
  assert MatrixVectorMultiply(a, v, n) == seq(n, i' requires 0 <= i' < n => Sum(seq(n, j requires 0 <= j < n => a[i'][j] * v[j])));
  forall i | 0 <= i < n {
    assert MatrixVectorMultiply(a, v, n)[i] == Sum(seq(n, j requires 0 <= j < n => a[i][j] * v[j]));
  }
}

/* helper modified by LLM (iteration 5): pointwise unfolding for MatrixMultiply */
lemma MatrixMultiplyIndex(a: Matrix, b: Matrix, n: nat)
  requires IsSquareMatrix(a, n) && IsSquareMatrix(b, n)
  ensures forall i, j :: 0 <= i < n && 0 <= j < n ==> MatrixMultiply(a, b, n)[i][j] == Sum(seq(n, k requires 0 <= k < n => a[i][k] * b[k][j]))
{
  // Unfold the function definition for MatrixMultiply to expose the double-indexed sum
  assert MatrixMultiply(a, b, n) == seq(n, i' requires 0 <= i' < n => seq(n, j' requires 0 <= j' < n => Sum(seq(n, k requires 0 <= k < n => a[i'][k] * b[k][j']))));
  forall i, j | 0 <= i < n && 0 <= j < n {
    assert MatrixMultiply(a, b, n)[i][j] == Sum(seq(n, k requires 0 <= k < n => a[i][k] * b[k][j]));
  }
}

/* helper modified by LLM (iteration 5): identity matrix acts as identity on vectors */
lemma IdentityActs(m: Matrix, v: Vector, n: nat)
  requires IsSquareMatrix(m, n) && IsVector(v, n) && IsIdentityMatrix(m, n)
  ensures MatrixVectorMultiply(m, v, n) == v
{
  MatrixVectorMultiplyIndex(m, v, n);
  forall i | 0 <= i < n {
    calc {
      MatrixVectorMultiply(m, v, n)[i];
      == Sum(seq(n, j requires 0 <= j < n => m[i][j] * v[j]));
      == Sum(seq(n, j requires 0 <= j < n => (if i == j then 1.0 else 0.0) * v[j]));
      == Sum(seq(n, j requires 0 <= j < n => (if i == j then v[j] else 0.0)));
      == v[i];
    }
  }
}

/* helper modified by LLM (iteration 5): inverse produces solution and uniqueness */
lemma InverseSolvesAndUnique(a: Matrix, a_inv: Matrix, b: Vector, n: nat)
  requires IsSquareMatrix(a, n) && IsSquareMatrix(a_inv, n) && IsVector(b, n) && AreInverses(a, a_inv, n)
  ensures MatrixVectorMultiply(a, MatrixVectorMultiply(a_inv, b, n), n) == b
  ensures forall y :: IsVector(y, n) && MatrixVectorMultiply(a, y, n) == b ==> y == MatrixVectorMultiply(a_inv, b, n)
{
  // Forward direction: a * (a_inv * b) = b
  MatrixMultiplyIndex(a, a_inv, n);
  MatrixVectorMultiplyIndex(a_inv, b, n);
  MatrixVectorMultiplyIndex(a, MatrixVectorMultiply(a_inv, b, n), n);

  forall i | 0 <= i < n {
    var lhs := MatrixVectorMultiply(a, MatrixVectorMultiply(a_inv, b, n), n)[i];
    assert lhs == Sum(seq(n, j requires 0 <= j < n => a[i][j] * MatrixVectorMultiply(a_inv, b, n)[j]));
    assert MatrixVectorMultiply(a_inv, b, n) == seq(n, j' requires 0 <= j' < n => Sum(seq(n, k requires 0 <= k < n => a_inv[j'][k] * b[k])));
    assert lhs == Sum(seq(n, j requires 0 <= j < n => a[i][j] * Sum(seq(n, k requires 0 <= k < n => a_inv[j][k] * b[k]))));

    // Swap sums and factor b[k]
    assert lhs == Sum(seq(n, k requires 0 <= k < n => (Sum(seq(n, j requires 0 <= j < n => a[i][j] * a_inv[j][k])) * b[k])));
    // Replace inner sum by matrix product entry using MatrixMultiplyIndex
    MatrixMultiplyIndex(a, a_inv, n);
    assert lhs == Sum(seq(n, k requires 0 <= k < n => MatrixMultiply(a, a_inv, n)[i][k] * b[k]));

    // Since a * a_inv = I, this equals b[i]
    assert IsIdentityMatrix(MatrixMultiply(a, a_inv, n), n);
    IdentityActs(MatrixMultiply(a, a_inv, n), b, n);
    assert lhs == b[i];
  }

  // Uniqueness: if a * y = b then y = a_inv * b
  MatrixMultiplyIndex(a_inv, a, n);
  MatrixVectorMultiplyIndex(a_inv, b, n);
  // For any such y, show pointwise equality
  forall y | IsVector(y, n) && MatrixVectorMultiply(a, y, n) == b {
    assert MatrixVectorMultiply(a_inv, b, n) == MatrixVectorMultiply(a_inv, MatrixVectorMultiply(a, y, n), n);

    forall i0 | 0 <= i0 < n {
      var lhs2 := MatrixVectorMultiply(a_inv, MatrixVectorMultiply(a, y, n), n)[i0];
      assert lhs2 == Sum(seq(n, j requires 0 <= j < n => a_inv[i0][j] * MatrixVectorMultiply(a, y, n)[j]));
      assert MatrixVectorMultiply(a, y, n) == seq(n, j' requires 0 <= j' < n => Sum(seq(n, k requires 0 <= k < n => a[j'][k] * y[k])));
      assert lhs2 == Sum(seq(n, j requires 0 <= j < n => a_inv[i0][j] * Sum(seq(n, k requires 0 <= k < n => a[j][k] * y[k]))));

      // Swap sums and apply MatrixMultiplyIndex(a_inv, a, n)
      assert lhs2 == Sum(seq(n, k requires 0 <= k < n => (Sum(seq(n, j requires 0 <= j < n => a_inv[i0][j] * a[j][k])) * y[k])));
      MatrixMultiplyIndex(a_inv, a, n);
      assert lhs2 == Sum(seq(n, k requires 0 <= k < n => MatrixMultiply(a_inv, a, n)[i0][k] * y[k]));

      // a_inv * a = I, so this equals y[i0]
      assert IsIdentityMatrix(MatrixMultiply(a_inv, a, n), n);
      IdentityActs(MatrixMultiply(a_inv, a, n), y, n);
      assert lhs2 == y[i0];
    }

    // Pointwise equality yields vector equality
    assert MatrixVectorMultiply(a_inv, b, n) == y;
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
  /* code modified by LLM (iteration 5): compute solution using existential inverse witness */
  var a_inv :| IsSquareMatrix(a_inv, n) && AreInverses(a, a_inv, n);
  x := MatrixVectorMultiply(a_inv, b, n);
  InverseSolvesAndUnique(a, a_inv, b, n);
}

// </vc-code>
