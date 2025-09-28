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
/* helper modified by LLM (iteration 5): simple identity function for Float, kept for completeness */
function IdFloat(x: Float): Float
  ensures IdFloat(x) == x
{
  x
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
  /* code modified by LLM (iteration 5): replace sequence comprehensions with loops building the outer matrix */
  var res: seq<seq<Float>> := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |res| == i
    invariant forall ii :: 0 <= ii < |res| ==> |res[ii]| == |b|
    invariant forall ii, j :: 0 <= ii < |res| && 0 <= j < |b| ==> res[ii][j] == op(a[ii], b[j])
    decreases |a| - i
  {
    var row: seq<Float> := [];
    var j := 0;
    while j < |b|
      invariant 0 <= j <= |b|
      invariant |row| == j
      invariant forall jj :: 0 <= jj < j ==> row[jj] == op(a[i], b[jj])
      decreases |b| - j
    {
      row := row + [op(a[i], b[j])];
      j := j + 1;
    }
    res := res + [row];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
