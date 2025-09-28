// <vc-preamble>
/*
* Universal function outer method implementation for applying binary operators
* to all pairs of elements from two input vectors, producing a matrix result.
* Generalizes the concept of outer product beyond just multiplication.
*/

// Float type to match Lean's Float semantics
newtype Float = real

// Binary operator function type for Float numbers
type BinaryOp = (Float, Float) -> Float

// Method that applies a binary operator to all pairs (a[i], b[j])
// from input vectors a and b, producing an m×n matrix result
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): recursive row builder */
function BuildRowRec(op: BinaryOp, a: seq<Float>, b: seq<Float>, i: int, n: int): seq<Float>
  requires 0 <= i < |a|
  requires 0 <= n <= |b|
  ensures |result| == n
  ensures forall j :: 0 <= j < n ==> result[j] == op(a[i], b[j])
  decreases n
{
  if n == 0 then [] else BuildRowRec(op, a, b, i, n-1) + [op(a[i], b[n-1])]
}

/* helper modified by LLM (iteration 5): builds full row using BuildRowRec */
function BuildRow(op: BinaryOp, a: seq<Float>, b: seq<Float>, i: int): seq<Float>
  requires 0 <= i < |a|
  ensures |result| == |b|
  ensures forall j :: 0 <= j < |b| ==> result[j] == op(a[i], b[j])
{
  BuildRowRec(op, a, b, i, |b|)
}

/* helper modified by LLM (iteration 5): recursive matrix builder */
function BuildMatrixRec(op: BinaryOp, a: seq<Float>, b: seq<Float>, m: int): seq<seq<Float>>
  requires 0 <= m <= |a|
  ensures |result| == m
  ensures forall i :: 0 <= i < m ==> |result[i]| == |b|
  ensures forall i, j :: 0 <= i < m && 0 <= j < |b| ==> result[i][j] == op(a[i], b[j])
  decreases m
{
  if m == 0 then [] else BuildMatrixRec(op, a, b, m-1) + [BuildRow(op, a, b, m-1)]
}

/* helper modified by LLM (iteration 5): builds full matrix using BuildMatrixRec */
function BuildMatrix(op: BinaryOp, a: seq<Float>, b: seq<Float>): seq<seq<Float>>
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |a| ==> |result[i]| == |b|
  ensures forall i, j :: 0 <= i < |a| && 0 <= j < |b| ==> result[i][j] == op(a[i], b[j])
{
  BuildMatrixRec(op, a, b, |a|)
}

// </vc-helpers>

// <vc-spec>
method Outer(op: BinaryOp, a: seq<Float>, b: seq<Float>) returns (result: seq<seq<Float>>)
  requires true  // No preconditions - works for any vectors and binary operation
  ensures |result| == |a|  // Result has same number of rows as length of first vector
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == |b|  // Each row has same length as second vector
  ensures forall i, j :: 0 <= i < |a| && 0 <= j < |b| ==> result[i][j] == op(a[i], b[j])  // Each element is op applied to corresponding pair
  ensures forall i :: 0 <= i < |a| ==> (forall j :: 0 <= j < |b| ==> 
    exists ai, bj :: ai == a[i] && bj == b[j] && result[i][j] == op(ai, bj))  // Structural property: represents Cartesian product
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): construct result by building full matrix using helpers */
  result := BuildMatrix(op, a, b);
}

// </vc-code>
