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
// Helper function to create a row by applying the binary operator
// to a single element from vector a and all elements from vector b
function CreateRow(op: BinaryOp, ai: Float, b: seq<Float>): seq<Float>
  ensures |CreateRow(op, ai, b)| == |b|
  ensures forall j :: 0 <= j < |b| ==> CreateRow(op, ai, b)[j] == op(ai, b[j])
{
  seq(|b|, j requires 0 <= j < |b| => op(ai, b[j]))
}

/* helper modified by LLM (iteration 5): simplified lemma with explicit proof body */
lemma StructuralPropertyLemma(op: BinaryOp, a: seq<Float>, b: seq<Float>, result: seq<seq<Float>>)
  requires |result| == |a|
  requires forall i :: 0 <= i < |result| ==> |result[i]| == |b|
  requires forall i, j :: 0 <= i < |a| && 0 <= j < |b| ==> result[i][j] == op(a[i], b[j])
  ensures forall i :: 0 <= i < |a| ==> (forall j :: 0 <= j < |b| ==> 
    exists ai, bj :: ai == a[i] && bj == b[j] && result[i][j] == op(ai, bj))
{
  forall i | 0 <= i < |a|
    ensures forall j :: 0 <= j < |b| ==> 
      exists ai, bj :: ai == a[i] && bj == b[j] && result[i][j] == op(ai, bj)
  {
    forall j | 0 <= j < |b|
      ensures exists ai, bj :: ai == a[i] && bj == b[j] && result[i][j] == op(ai, bj)
    {
      var ai := a[i];
      var bj := b[j];
      assert ai == a[i] && bj == b[j] && result[i][j] == op(ai, bj);
    }
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
  /* code modified by LLM (iteration 5): explicit construction with lemma call */
  result := seq(|a|, i requires 0 <= i < |a| => CreateRow(op, a[i], b));
  
  StructuralPropertyLemma(op, a, b, result);
}
// </vc-code>
