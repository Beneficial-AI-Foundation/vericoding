// <vc-preamble>
// Type alias for binary operations on real numbers
type BinaryOp = (real, real) -> real

// Method representing ufunc.__call__ for binary operations on vectors
// </vc-preamble>

// <vc-helpers>

function min(a: int, b: int): int { if a < b then a else b }

lemma ResultLengthLemma(op: BinaryOp, a: seq<real>, b: seq<real>, index: int) 
  requires |a| == |b|
  requires 0 <= index <= |a|
  ensures forall i :: 0 <= i < index ==> op(a[i], b[i]) is real
{
}

/* helper modified by LLM (iteration 2): Added index parameter to lemma */

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
  /* code modified by LLM (iteration 2): Fixed loop index bound verification */
  var len := |a|;
  result := [];
  var index := 0;
  
  while index < len
    invariant 0 <= index <= len
    invariant |result| == index
    invariant forall j :: 0 <= j < index ==> result[j] == op(a[j], b[j])
  {
    ResultLengthLemma(op, a, b, index + 1);
    var elem := op(a[index], b[index]);
    result := result + [elem];
    index := index + 1;
  }
}
// </vc-code>
