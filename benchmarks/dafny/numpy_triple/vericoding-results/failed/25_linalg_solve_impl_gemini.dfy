// <vc-preamble>
type Matrix = seq<seq<real>>
type Vector = seq<real>

// Check if a matrix is square with given dimension
predicate IsSquareMatrix(a: Matrix, n: nat)
{
    |a| == n && forall i :: 0 <= i < n ==> |a[i]| == n
}

// Check if a vector has given dimension
predicate IsVector(v: Vector, n: nat)
{
    |v| == n
}

// Matrix-vector multiplication: compute (a * v)[i]
function MatrixVectorMultiply(a: Matrix, v: Vector, i: nat): real
    requires 0 <= i < |a|
    requires |a| > 0 && |a[i]| == |v|
{
    if |v| == 0 then 0.0
    else SumProduct(a[i], v, 0)
}

// Helper function for computing dot product
function SumProduct(row: seq<real>, v: Vector, idx: nat): real
    requires |row| == |v|
    decreases |row| - idx
{
    if idx >= |row| then 0.0
    else row[idx] * v[idx] + SumProduct(row, v, idx + 1)
}

// Matrix multiplication for square matrices
function MatrixMultiply(a: Matrix, b: Matrix, i: nat, j: nat): real
    requires IsSquareMatrix(a, |a|) && IsSquareMatrix(b, |a|)
    requires 0 <= i < |a| && 0 <= j < |a|
{
    SumProduct(a[i], GetColumn(b, j), 0)
}

// Extract column j from matrix
function GetColumn(m: Matrix, j: nat): Vector
    requires IsSquareMatrix(m, |m|) && 0 <= j < |m|
{
    seq(|m|, i requires 0 <= i < |m| => m[i][j])
}

// Identity matrix predicate
predicate IsIdentityMatrix(m: Matrix)
    requires IsSquareMatrix(m, |m|)
{
    forall i, j :: 0 <= i < |m| && 0 <= j < |m| ==>
        m[i][j] == (if i == j then 1.0 else 0.0)
}

// Matrix invertibility predicate
ghost predicate IsInvertible(a: Matrix)
    requires IsSquareMatrix(a, |a|)
{
    exists a_inv :: IsSquareMatrix(a_inv, |a|) &&
        // a * a_inv = I
        (forall i, j :: 0 <= i < |a| && 0 <= j < |a| ==>
            MatrixMultiply(a, a_inv, i, j) == (if i == j then 1.0 else 0.0)) &&
        // a_inv * a = I  
        (forall i, j :: 0 <= i < |a| && 0 <= j < |a| ==>
            MatrixMultiply(a_inv, a, i, j) == (if i == j then 1.0 else 0.0))
}

// Check if vector x satisfies ax = b
predicate SatisfiesEquation(a: Matrix, x: Vector, b: Vector)
    requires IsSquareMatrix(a, |a|) && IsVector(x, |a|) && IsVector(b, |a|)
{
    forall i :: 0 <= i < |a| ==>
        MatrixVectorMultiply(a, x, i) == b[i]
}
// </vc-preamble>

// <vc-helpers>
function Identity(n: nat): Matrix
{
    seq(n, i => seq(n, j => if i == j then 1.0 else 0.0))
}

function MatrixVectorMultiplyVector(a: Matrix, v: Vector): Vector
    requires |a| > 0 && IsSquareMatrix(a, |a|) && IsVector(v, |a|)
{
    seq(|a|, i => MatrixVectorMultiply(a, v, i))
}

function MatrixMultiplyMatrix(a: Matrix, b: Matrix): Matrix
    requires |a| > 0 && IsSquareMatrix(a, |a|) && IsSquareMatrix(b, |a|)
{
    seq(|a|, i => seq(|a|, j => MatrixMultiply(a, b, i, j)))
}

lemma Lemma_MatrixVectorAssociativity(a: Matrix, b: Matrix, v: Vector)
    requires |a| > 0 && IsSquareMatrix(a, |a|) && IsSquareMatrix(b, |a|) && IsVector(v, |a|)
    ensures MatrixVectorMultiplyVector(a, MatrixVectorMultiplyVector(b, v)) ==
            MatrixVectorMultiplyVector(MatrixMultiplyMatrix(a, b), v)
{}

lemma Lemma_IdentityMultiplyVector(n: nat, v: Vector)
    requires n > 0 && IsVector(v, n)
    ensures MatrixVectorMultiplyVector(Identity(n), v) == v
{}
// </vc-helpers>

// <vc-spec>
method Solve(a: Matrix, b: Vector) returns (x: Vector)
    requires IsSquareMatrix(a, |a|) && |a| > 0
    requires IsVector(b, |a|)
    requires IsInvertible(a)
    ensures IsVector(x, |a|)
    ensures SatisfiesEquation(a, x, b)
    ensures forall y :: IsVector(y, |a|) && SatisfiesEquation(a, y, b) ==> y == x
    ensures forall a_inv :: (IsSquareMatrix(a_inv, |a|) &&
        (forall i, j :: 0 <= i < |a| && 0 <= j < |a| ==>
            MatrixMultiply(a, a_inv, i, j) == (if i == j then 1.0 else 0.0))) ==>
        (forall i :: 0 <= i < |a| ==>
            x[i] == MatrixVectorMultiply(a_inv, b, i))
// </vc-spec>
// <vc-code>
{
  ghost var n := |a|;
  ghost var a_inv: Matrix;
  ghost var sol: Vector;

  ghost {
    a_inv :|  
        IsSquareMatrix(a_inv, n) &&
        (forall i, j :: 0 <= i < n && 0 <= j < n ==>
            MatrixMultiply(a, a_inv, i, j) == (if i == j then 1.0 else 0.0)) &&
        (forall i, j :: 0 <= i < n && 0 <= j < n ==>
            MatrixMultiply(a_inv, a, i, j) == (if i == j then 1.0 else 0.0));
    sol := seq(n, i => MatrixVectorMultiply(a_inv, b, i));
  }

  ghost {
    // Prove SatisfiesEquation(a, sol, b)
    Lemma_MatrixVectorAssociativity(a, a_inv, b);
    Lemma_IdentityMultiplyVector(n, b);
    calc == {
      MatrixVectorMultiplyVector(a, sol);
      MatrixVectorMultiplyVector(a, MatrixVectorMultiplyVector(a_inv, b));
      MatrixVectorMultiplyVector(MatrixMultiplyMatrix(a, a_inv), b);
      MatrixVectorMultiplyVector(Identity(n), b);
      b;
    }
    assert SatisfiesEquation(a, sol, b);

    // Prove uniqueness
    forall y | IsVector(y, n) && SatisfiesEquation(a, y, b)
      ensures y == sol
    {
      Lemma_MatrixVectorAssociativity(a_inv, a, y);
      Lemma_IdentityMultiplyVector(n, y);
      calc == {
        y;
        MatrixVectorMultiplyVector(Identity(n), y);
        MatrixVectorMultiplyVector(MatrixMultiplyMatrix(a_inv, a), y);
        MatrixVectorMultiplyVector(a_inv, MatrixVectorMultiplyVector(a, y));
        MatrixVectorMultiplyVector(a_inv, b);
        sol;
      }
    }

    // Prove the final ensures about any right inverse
    forall a_inv_cand | IsSquareMatrix(a_inv_cand, n) &&
                       (forall i', j' :: 0 <= i' < n && 0 <= j' < n ==>
                          MatrixMultiply(a, a_inv_cand, i', j') == (if i' == j' then 1.0 else 0.0))
      ensures forall i' :: 0 <= i' < n ==> sol[i'] == MatrixVectorMultiply(a_inv_cand, b, i')
    {
       var z := seq(n, i' => MatrixVectorMultiply(a_inv_cand, b, i'));
       Lemma_MatrixVectorAssociativity(a, a_inv_cand, b);
       Lemma_IdentityMultiplyVector(n, b);
       assert SatisfiesEquation(a, z, b);
       assert z == sol; // By uniqueness proven above
    }
  }

  x := sol;
}
// </vc-code>
