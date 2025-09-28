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
type ArrayMatrix = array<array<real>>
type ArrayVector = array<real>

method Augment(a: ArrayMatrix, b: ArrayVector, n: nat) returns (res: ArrayMatrix)
  requires IsSquareMatrix(SeqOfMatrix(a), n) && IsVector(SeqOfVector(b), n)
  ensures |res.Length| == n
  ensures forall i :: 0 <= i < n ==> |res[i].Length| == n+1
{
  /* helper modified by LLM (iteration 3): fixed compilation errors by using loops to avoid side-effect constructors in lambda expressions */
  res := new array<array<real>>[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> res[k] != null && res[k].Length == n+1
  {
    res[i] := new array<real>[n+1];
    var j := 0;
    while j < n+1
      invariant 0 <= j <= n+1
      invariant res[i] != null && res[i].Length == n+1
    {
      if j < n {
        res[i][j] := a[i][j];
      } else {
        res[i][j] := b[i];
      }
      j := j + 1;
    }
    i := i + 1;
  }
}

method Eliminate(aug: ArrayMatrix, n: nat) returns (res: ArrayMatrix)
  requires aug.Length == n && forall i :: 0 <= i < n ==> aug[i].Length == n+1
  ensures res.Length == n && forall i :: 0 <= i < n ==> res[i].Length == n+1
  ensures forall i :: 0 <= i < n ==> res[i][i] != 0.0
  ensures forall i,j :: 0 <= i < n && 0 <= j < n && i > j ==> res[i][j] == 0.0
{
  /* helper modified by LLM (iteration 3): added invariants for verification */
  var current := aug;
  var col := 0;
  while col < n
    invariant 0 <= col <= n
    invariant current.Length == n && forall i :: 0 <= i < n ==> current[i].Length == n+1
    invariant forall c :: 0 <= c < col ==> current[c][c] != 0.0
    invariant forall c1, c2 :: 0 <= c1 < n && 0 <= c2 < n && c1 > c2 && c2 < col ==> current[c1][c2] == 0.0
  {
    var pivot := -1;
    var k := col;
    while k < n
    {
      if current[k][col] != 0.0 {
        pivot := k;
        break;
      }
      k := k + 1;
    }
    if pivot != -1 {
      var temp := current[pivot];
      current[pivot] := current[col];
      current[col] := temp;
      for r := col + 1 to n-1
      {
        var factor := current[r][col] / current[col][col];
        for c := col to n
        {
          current[r][c] := current[r][c] - factor * current[col][c];
        }
      }
    }
    col := col + 1;
  }
  res := current;
}

/* helper modified by LLM (iteration 5): fixed syntax error in invariant by correcting sum expression */
method BackSubstitute(upper: ArrayMatrix, n: nat) returns (x: ArrayVector)
  requires upper.Length == n && forall i :: 0 <= i < n ==> upper[i].Length == n+1
  requires forall i :: 0 <= i < n ==> upper[i][i] != 0.0
  requires forall i,j :: 0 <= i < n && 0 <= j < n && i > j ==> upper[i][j] == 0.0
  ensures x.Length == n
{
  /* helper modified by LLM (iteration 4): removed duplicate predicates and added invariant for inner loop to fix compilation errors */
  var x_arr: ArrayVector := new array<real>[n](_ => 0.0);
  var i := n-1;
  while i >= 0
    decreases i
    invariant -1 <= i < n
    invariant forall k :: i+1 <= k < n ==> x_arr[k] == (upper[k][n] - Sum(seq(j | k+1 <= j < n :: upper[k][j] * x_arr[j]))) / upper[k][k]
  {
    var sum := 0.0;
    var j := i+1;
    while j < n
      invariant i+1 <= j <= n
    {
      sum := sum + upper[i][j] * x_arr[j];
      j := j + 1;
    }
    x_arr[i] := (upper[i][n] - sum) / upper[i][i];
    i := i - 1;
  }
  x := x_arr;
}

// Helper functions to convert arrays to sequences for verification
function SeqOfMatrix(a: ArrayMatrix): Matrix
  ensures |SeqOfMatrix(a)| == a.Length
  ensures forall i :: 0 <= i < a.Length ==> |SeqOfMatrix(a)[i]| == a[i].Length
{
  seq(a.Length, i requires 0 <= i < a.Length && a[i] != null => seq(a[i].Length, j requires 0 <= j < a[i].Length => a[i][j]))
}

function SeqOfVector(a: ArrayVector): Vector
  ensures |SeqOfVector(a)| == a.Length
{
  seq(a.Length, i requires 0 <= i < a.Length => a[i])
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
/* code modified by LLM (iteration 3): fixed type errors and compilation by using loops for array initialization */
var a_arr: ArrayMatrix := new array<array<real>>[n];
for i := 0 to n-1 {
  a_arr[i] := new array<real>[n];
  for j := 0 to n-1 {
    a_arr[i][j] := a[i][j];
  }
}
var b_arr: ArrayVector := new array<real>[n];
for i := 0 to n-1 {
  b_arr[i] := b[i];
}
var aug := Augment(a_arr, b_arr, n);
var upper := Eliminate(aug, n);
var x_arr := BackSubstitute(upper, n);
x := seq(n, i requires 0 <= i < n => x_arr[i]);
// </vc-code>
