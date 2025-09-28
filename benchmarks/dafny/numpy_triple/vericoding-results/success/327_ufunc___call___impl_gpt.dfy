// <vc-preamble>
// Type alias for binary operations on real numbers
type BinaryOp = (real, real) -> real

// Method representing ufunc.__call__ for binary operations on vectors
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): establish index bound transfer between equal-length sequences */
lemma IndexBoundFromEqualLengths(i: int, a: seq<real>, b: seq<real>)
  requires |a| == |b|
  requires 0 <= i < |a|
  ensures 0 <= i < |b|
{
}
// </vc-helpers>

// <vc-spec>
method UfuncCall(op: BinaryOp, a: seq<real>, b: seq<real>) returns (result: seq<real>)
  // Input vectors must have the same length
  requires |a| == |b|
  // Result has the same length as input vectors
  ensures |result| == |a|
  // Each element in the result is computed by applying the operation
  // to corresponding elements from the input vectors
  ensures forall i :: 0 <= i < |result| ==> result[i] == op(a[i], b[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): build result with loop and sequence concatenation, maintaining invariants */
  var r: seq<real> := [];
  var i: int := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==> r[j] == op(a[j], b[j])
  {
    r := r + [op(a[i], b[i])];
    i := i + 1;
  }
  result := r;
}
// </vc-code>
