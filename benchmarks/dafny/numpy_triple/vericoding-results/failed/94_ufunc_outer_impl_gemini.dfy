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
/* helper modified by LLM (iteration 5): Keeping correct implementation. */
method GenerateRow(op: BinaryOp, a_i: Float, b: seq<Float>) returns (row: seq<Float>)
  ensures |row| == |b|
  ensures forall j :: 0 <= j < |b| ==> row[j] == op(a_i, b[j])
{
  row := [];
  var j := 0;
  while j < |b|
    invariant 0 <= j <= |b|
    invariant |row| == j
    invariant forall k :: 0 <= k < j ==> row[k] == op(a_i, b[k])
  {
    row := row + [op(a_i, b[j])];
    j := j + 1;
  }
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
  /* code modified by LLM (iteration 5): Removed redundant loop invariant and used a forall statement to prove the postcondition. */
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> |result[k]| == |b|
    invariant forall k, l :: 0 <= k < i && 0 <= l < |b| ==> result[k][l] == op(a[k], b[l])
  {
    var newRow := GenerateRow(op, a[i], b);
    result := result + [newRow];
    i := i + 1;
  }

  forall i', j' | 0 <= i' < |a| && 0 <= j' < |b|
    ensures exists ai, bj :: ai == a[i'] && bj == b[j'] && result[i'][j'] == op(ai, bj)
  {
  }
}
// </vc-code>
