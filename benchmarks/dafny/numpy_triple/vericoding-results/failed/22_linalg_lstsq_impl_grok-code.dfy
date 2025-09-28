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
/* helper modified by LLM (iteration 2): Added requires for matrix uniformity to fix index out of range */

function Transpose(A: Matrix): Matrix
    requires |A| > 0
    requires forall i :: 0 <= i < |A| ==> |A[i]| == |A[0]|
    ensures |Transpose(A)| == |A[0]|
    ensures forall i :: 0 <= i < |A[0]| ==> |Transpose(A)[i]| == |A|
    ensures forall i,j :: 0 <= i < |A[0]| && 0 <= j < |A| ==> Transpose(A)[i][j] == A[j][i]
{
    seq(|A[0]|, i requires 0 <= i < |A[0]| => seq(|A|, j requires 0 <= j < |A| => A[j][i]) )
}

function MatMul(A: Matrix, B: Matrix): Matrix
    requires |A| > 0 && |B| > 0
    requires forall i :: 0 <= i < |A| ==> |A[i]| == |B|
    requires forall i :: 0 <= i < |B| ==> |B[i]| == |B[0]|
    ensures |MatMul(A, B)| == |A|
    ensures forall i :: 0 <= i < |A| ==> |MatMul(A, B)[i]| == |B[0]|
    ensures forall i,k :: 0 <= i < |A| && 0 <= k < |B[0]| ==> MatMul(A, B)[i][k] == DotProduct(A[i], seq(|B|, j requires 0 <= j < |B| => B[j][k]))
{
    seq(|A|, i requires 0 <= i < |A| => seq(|B[0]|, k requires 0 <= k < |B[0]| => DotProduct(A[i], seq(|B|, j requires 0 <= j < |B| => B[j][k])) ) )
}

/* helper modified by LLM (iteration 3): Added helper functions for computing determinant and Crame\'s rule to solve the linear system */

function Det(A: Matrix): real
    requires |A| > 0
    requires |A| == |A[0]|
    requires forall i :: 0 <= i < |A| ==> |A[i]| == |A|
    decreases |A|
{
    if |A| == 1 then A[0][0]
    else if |A| == 2 then A[0][0] * A[1][1] - A[0][1] * A[1][0]
    else DetRec(A, 0, 1.0)
}

function DetRec(A: Matrix, j: nat, sign: real): real
    requires |A| > 0
    requires |A| == |A[0]|
    requires forall i :: 0 <= i < |A| ==> |A[i]| == |A|
    requires j <= |A|
    decreases |A|, j
{
    if |A| == 1 then 0.0
    else if j == |A| then 0.0
    else sign * A[0][j] * Det(Minor(A, 0, j)) + DetRec(A, j + 1, -sign)
}

/* helper modified by LLM (iteration 5): Fixed syntax error by changing var n = |A| to var n := |A| */

function Minor(A: Matrix, r: nat, c: nat): Matrix
    requires |A| > 0
    requires |A| == |A[0]|
    requires 0 <= r < |A|
    requires 0 <= c < |A|
    ensures |Minor(A, r, c)| == |A| - 1
    ensures forall i :: 0 <= i < |Minor(A, r, c)| ==> |Minor(A, r, c)[i]| == |A| - 1
    ensures forall i,j :: 0 <= i < |Minor(A, r, c)| && 0 <= j < |Minor(A, r, c)| ==> Minor(A, r, c)[i][j] == A[if i < r then i else i + 1][if j < c then j else j + 1]
{
    var n := |A|;
    seq(n-1, i requires 0 <= i < n-1 => seq(n-1, j requires 0 <= j < n-1 => A[if i < r then i else i + 1][if j < c then j else j + 1]))
}

/* helper modified by LLM (iteration 5): Fixed syntax error by changing var n = |A| to var n := |A| */

function ReplaceColumn(A: Matrix, j: nat, v: Vector): Matrix
    requires |A| > 0
    requires |A| == |A[0]|
    requires 0 <= j < |A|
    requires |v| == |A|
    ensures |ReplaceColumn(A, j, v)| == |A|
    ensures forall i :: 0 <= i < |A| ==> |ReplaceColumn(A, j, v)[i]| == |A[i]|
    ensures forall i,k :: 0 <= i < |A| && 0 <= k < |A| && k != j ==> ReplaceColumn(A, j, v)[i][k] == A[i][k]
    ensures forall i :: 0 <= i < |A| ==> ReplaceColumn(A, j, v)[i][j] == v[i]
{
    var n := |A|;
    seq(n, i requires 0 <= i < n => seq(n, k requires 0 <= k < n => if k == j then v[i] else A[i][k]))
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
/* code modified by LLM (iteration 3): Implemented computing x using Cramere\'s rule by solving ATA x = ATB */
{
    var AT := Transpose(a);
    var ATA := MatMul(AT, a);
    var ATB := MatVecMul(AT, b);
    x := seq(|a[0]|, i requires 0 <= i < |a[0]| => Det(ReplaceColumn(ATA, i, ATB)) / Det(ATA));
}
// </vc-code>
