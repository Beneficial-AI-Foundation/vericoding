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
/* helper modified by LLM (iteration 5): column extractor */
function Col(a: Matrix, j: int): Vector
    requires |a| > 0
    requires 0 <= j < |a[0]|
{
    seq(|a|, i => a[i][j])
}

/* helper modified by LLM (iteration 5): Gramian matrix */
function Gram(a: Matrix): Matrix
    requires |a| > 0
{
    var m := |a[0]|;
    seq(m, j => seq(m, k => DotProduct(Col(a, j), Col(a, k))))
}

/* helper modified by LLM (iteration 5): RHS for normal equations */
function Rhs(a: Matrix, b: Vector): Vector
    requires |a| > 0
    requires |a| == |b|
{
    var m := |a[0]|;
    seq(m, j => DotProduct(Col(a, j), b))
}

/* helper modified by LLM (iteration 5): solve normal equations via functional Gaussian elimination */
method SolveNormalSystem(a: Matrix, b: Vector) returns (x: Vector)
    requires |a| > 0
    requires |a| == |b|
    ensures |x| == |a[0]|
    ensures forall j :: 0 <= j < |x| ==> DotProduct(Col(a, j), VecSub(b, MatVecMul(a, x))) == 0.0
{
    var m := |a[0]|;
    var G := Gram(a);
    var h := Rhs(a, b);

    var U := G; // seq of rows
    var rhs := h;

    var i := 0;
    while i < m
      decreases m - i
      invariant 0 <= i <= m
      invariant |U| == m && |rhs| == m
    {
      if U[i][i] == 0.0 {
        var k := i + 1;
        while k < m && U[k][i] == 0.0
          decreases m - k
          invariant i+1 <= k <= m
        {
          k := k + 1;
        }
        if k < m {
          var rowi := U[i];
          var rowk := U[k];
          U := U[..i] + [rowk] + U[i+1..k] + [rowi] + U[k+1..];
          var ri := rhs[i];
          rhs := rhs[..i] + [rhs[k]] + rhs[i+1..k] + [ri] + rhs[k+1..];
        }
      }

      if U[i][i] == 0.0 {
        var newRow := seq(m, c => if c == i then 1.0 else 0.0);
        U := U[..i] + [newRow] + U[i+1..];
        rhs := rhs[..i] + [0.0] + rhs[i+1..];
      }

      var j := i + 1;
      while j < m
        decreases m - j
        invariant i+1 <= j <= m
        invariant |U| == m && |rhs| == m
      {
        var denom := U[i][i];
        var factor := if denom == 0.0 then 0.0 else U[j][i] / denom;
        var rowj := seq(m, col => U[j][col] - factor * U[i][col]);
        U := U[..j] + [rowj] + U[j+1..];
        rhs := rhs[..j] + [rhs[j] - factor * rhs[i]] + rhs[j+1..];
        j := j + 1;
      }

      i := i + 1;
    }

    var sol := seq(m, _ => 0.0);
    var ii := m - 1;
    while ii >= 0
      decreases ii + 1
      invariant -1 <= ii < m
      invariant |sol| == m
    {
      var sum := 0.0;
      var jj := ii + 1;
      while jj < m
        decreases m - jj
        invariant ii+1 <= jj <= m
      {
        sum := sum + U[ii][jj] * sol[jj];
        jj := jj + 1;
      }
      if U[ii][ii] != 0.0 {
        sol := sol[..ii] + [(rhs[ii] - sum) / U[ii][ii]] + sol[ii+1..];
      } else {
        sol := sol[..ii] + [0.0] + sol[ii+1..];
      }
      ii := ii - 1;
    }

    x := sol;
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
/* code modified by LLM (iteration 5): compute least-squares solution via normal equations */
{
  var m := |a[0]|;
  x := SolveNormalSystem(a, b);
}

// </vc-code>
