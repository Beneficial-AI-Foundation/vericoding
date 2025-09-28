// <vc-preamble>
// Looking at the parse error, the issue is that Dafny doesn't support generic parameters on subset types in the syntax used. I'll fix this by removing the generic type parameters and using simple type aliases instead, while preserving the intended semantics through method preconditions and postconditions.



// Vector type
type Vector = seq<real>

// Matrix type  
type Matrix = seq<Vector>

// Helper function to compute dot product of two vectors
function DotProduct(u: Vector, v: Vector): real
    requires |u| == |v|
{
    if |u| == 0 then 0.0
    else u[0] * v[0] + DotProduct(u[1..], v[1..])
}

// Matrix-vector multiplication
function MatVecMul(A: Matrix, x: Vector): Vector
    requires |A| > 0
    requires forall i :: 0 <= i < |A| ==> |A[i]| == |x|
{
    seq(|A|, i requires 0 <= i < |A| => DotProduct(A[i], x))
}

// Euclidean norm squared of a vector
function NormSq(v: Vector): real
{
    DotProduct(v, v)
}

// Vector subtraction
function VecSub(a: Vector, b: Vector): Vector
    requires |a| == |b|
{
    seq(|a|, i requires 0 <= i < |a| => a[i] - b[i])
}

// Main least-squares solver method
// </vc-preamble>

// <vc-helpers>
function Transpose(M: Matrix): Matrix {
  if |M| == 0 then []
  else seq(|M[0]|, j => seq(|M|, i => M[i][j]))
}

function MatMul(A: Matrix, B: Matrix): Matrix
  requires |A| > 0 && |B| > 0
  requires forall i :: 0 <= i < |A| ==> |A[i]| == |B|
{
  seq(|A|, i => 
    seq(|B[0]|, j => 
      DotProduct(A[i], seq(|B|, k => B[k][j]))
    )
  )
}

/* helper modified by LLM (iteration 5): added absolute value function for reals */
function Abs(x: real): real {
  if x < 0.0 then -x else x
}

/* helper modified by LLM (iteration 5): fixed if-then-else syntax */
method SolveLinearSystem(M: Matrix, b: Vector) returns (x: Vector)
  requires |M| > 0
  requires forall i :: 0 <= i < |M| ==> |M[i]| == |M|
  requires |b| == |M|
  ensures MatVecMul(M, x) == b
{
  var n := |M|;
  var A := M;
  var c := b;
  x := new real[n];
  
  for k := 0 to n-1
  {
    var pivot_row := k;
    for i := k+1 to n-1
    {
      if Abs(A[i][k]) > Abs(A[pivot_row][k]) then
      {
        pivot_row := i;
      }
    }
    
    if A[pivot_row][k] != 0.0 then
    {
      if pivot_row != k then
      {
        var tempA := A[k];
        A := A[k := A[pivot_row]][pivot_row := tempA];
        var tempc := c[k];
        c := c[k := c[pivot_row]][pivot_row := tempc];
      }
      
      var pivot_val := A[k][k];
      var new_row_k := A[k];
      new_row_k := seq(n, j => if j >= k then new_row_k[j] / pivot_val else new_row_k[j]);
      A := A[k := new_row_k];
      c := c[k := c[k] / pivot_val];
      
      for i := k+1 to n-1
      {
        var factor := A[i][k];
        if factor != 0.0 then
        {
          var new_row_i := A[i];
          new_row_i := seq(n, j => if j < k then new_row_i[j] else new_row_i[j] - factor * A[k][j]);
          A := A[i := new_row_i];
          c := c[i := c[i] - factor * c[k]];
        }
      }
    }
  }
  
  for i := n-1 downto 0
  {
    if A[i][i] == 0.0 then
    {
      x[i] := 0.0;
    }
    else
    {
      var sum := 0.0;
      for j := i+1 to n-1
      {
        sum := sum + A[i][j] * x[j];
      }
      x[i] := c[i] - sum;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method Lstsq(a: Matrix, b: Vector) returns (x: Vector)
    requires |a| > 0 && |b| > 0
    requires |a| == |b|
    requires forall i :: 0 <= i < |a| ==> |a[i]| > 0
    requires forall i :: 0 <= i < |a| ==> |a[i]| == |a[0]|
    ensures |x| == |a[0]|
    ensures forall y: Vector :: |y| == |a[0]| ==> 
        NormSq(VecSub(b, MatVecMul(a, x))) <= NormSq(VecSub(b, MatVecMul(a, y)))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): using normal equations to solve least squares */
  var aT := Transpose(a);
  var M := MatMul(aT, a);
  var c := MatVecMul(aT, b);
  x := SolveLinearSystem(M, c);
}
// </vc-code>
