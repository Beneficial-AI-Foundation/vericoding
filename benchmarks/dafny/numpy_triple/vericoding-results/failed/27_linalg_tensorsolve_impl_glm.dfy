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
/* helper modified by LLM (iteration 4): fixed bounds checking in quantifier expressions */
function SwapRow(m: Matrix, i: int, j: int, n: nat): Matrix
  requires IsSquareMatrix(m, n)
  requires 0 <= i < n && 0 <= j < n
  ensures IsSquareMatrix(SwapRow(m, i, j, n), n)
  ensures forall k :: 0 <= k < n && k != i && k != j ==> SwapRow(m, i, j, n)[k] == m[k]
  ensures SwapRow(m, i, j, n)[i] == m[j]
  ensures SwapRow(m, i, j, n)[j] == m[i]
{
  if i == j then m else
    m[i := m[j]][j := m[i]]
}

/* helper modified by LLM (iteration 4): fixed bounds checking in quantifier expressions */
function SwapVectorElement(v: Vector, i: int, j: int): Vector
  requires 0 <= i < |v| && 0 <= j < |v|
  ensures |SwapVectorElement(v, i, j)| == |v|
  ensures forall k :: 0 <= k < |v| && k != i && k != j ==> SwapVectorElement(v, i, j)[k] == v[k]
  ensures SwapVectorElement(v, i, j)[i] == v[j]
  ensures SwapVectorElement(v, i, j)[j] == v[i]
{
  if i == j then v else
    v[i := v[j]][j := v[i]]
}

/* helper modified by LLM (iteration 4): fixed bounds checking in quantifier expressions */
function MultiplyRow(m: Matrix, row: int, factor: real, n: nat): Matrix
  requires IsSquareMatrix(m, n)
  requires 0 <= row < n
  ensures IsSquareMatrix(MultiplyRow(m, row, factor, n), n)
  ensures forall i :: 0 <= i < n && i != row ==> MultiplyRow(m, row, factor, n)[i] == m[i]
  ensures forall j :: 0 <= j < n ==> MultiplyRow(m, row, factor, n)[row][j] == m[row][j] * factor
{
  m[row := seq(n, j requires 0 <= j < n => m[row][j] * factor)]
}

/* helper modified by LLM (iteration 4): fixed bounds checking in quantifier expressions */
function MultiplyVectorElement(v: Vector, i: int, factor: real): Vector
  requires 0 <= i < |v|
  ensures |MultiplyVectorElement(v, i, factor)| == |v|
  ensures forall j :: 0 <= j < |v| && j != i ==> MultiplyVectorElement(v, i, factor)[j] == v[j]
  ensures MultiplyVectorElement(v, i, factor)[i] == v[i] * factor
{
  v[i := v[i] * factor]
}

/* helper modified by LLM (iteration 4): fixed bounds checking in quantifier expressions */
function AddRowMultiple(m: Matrix, target: int, source: int, factor: real, n: nat): Matrix
  requires IsSquareMatrix(m, n)
  requires 0 <= target < n && 0 <= source < n
  ensures IsSquareMatrix(AddRowMultiple(m, target, source, factor, n), n)
  ensures forall i :: 0 <= i < n && i != target ==> AddRowMultiple(m, target, source, factor, n)[i] == m[i]
  ensures forall j :: 0 <= j < n ==> 
          AddRowMultiple(m, target, source, factor, n)[target][j] == m[target][j] + factor * m[source][j]
{
  m[target := seq(n, j requires 0 <= j < n => m[target][j] + factor * m[source][j])]
}

/* helper modified by LLM (iteration 4): fixed bounds checking in quantifier expressions */
function AddVectorMultiple(v: Vector, target: int, source: int, factor: real): Vector
  requires 0 <= target < |v| && 0 <= source < |v|
  ensures |AddVectorMultiple(v, target, source, factor)| == |v|
  ensures forall i :: 0 <= i < |v| && i != target ==> AddVectorMultiple(v, target, source, factor)[i] == v[i]
  ensures AddVectorMultiple(v, target, source, factor)[target] == v[target] + factor * v[source]
{
  v[target := v[target] + factor * v[source]]
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
  /* code modified by LLM (iteration 4): fixed quantifier bounds and triggers */
  var a_work := a;
  var b_work := b;

  // Forward elimination
  for j := 0 to n-1
    invariant 0 <= j <= n
    invariant forall i {:trigger a_work[i][i]} :: 0 <= i < j ==> forall k :: i+1 <= k < n ==> a_work[k][i] == 0.0
  {
    // Find pivot row
    var pivot_row := j;
    var i := j;
    while i < n
      invariant j <= i <= n
      invariant pivot_row >= j && pivot_row < n
      invariant if pivot_row == j then forall k :: j <= k < i ==> a_work[k][j] == 0.0 else true
    {
      if a_work[i][j] != 0.0 {
        pivot_row := i;
        i := n;
      } else {
        i := i + 1;
      }
    }
    
    if pivot_row != j {
      a_work := SwapRow(a_work, j, pivot_row, n);
      b_work := SwapVectorElement(b_work, j, pivot_row);
    }

    // Eliminate column j
    if j < n-1 {
      for i := j+1 to n-1
        invariant j+1 <= i <= n
        invariant forall k :: j+1 <= k < i ==> a_work[k][j] == 0.0
      {
        if a_work[i][j] != 0.0 {
          var factor := a_work[i][j] / a_work[j][j];
          a_work := AddRowMultiple(a_work, i, j, -factor, n);
          b_work := AddVectorMultiple(b_work, i, j, -factor);
        }
      }
    }
  }

  // Back substitution
  var x_seq := seq(n, i => 0.0);
  for i := n-1 downto 0
    invariant -1 <= i < n
    invariant forall k :: i+1 <= k < n ==> 
            x_seq[k] == (b_work[k] - Sum(seq(n, l requires k+1 <= l < n => a_work[k][l] * x_seq[l]))) / a_work[k][k]
  {
    var s := 0.0;
    for j := i+1 to n-1
      invariant i+1 <= j <= n
      invariant s == Sum(seq(n, l requires i+1 <= l < j => a_work[i][l] * x_seq[l]))
    {
      s := s + a_work[i][j] * x_seq[j];
    }
    x_seq := x_seq[i := (b_work[i] - s) / a_work[i][i]];
  }

  return x_seq;
}
// </vc-code>
