// <vc-preamble>
// Method to compute absolute values element-wise for a sequence of real numbers
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): absolute value function for reals */
function abs(r: real): real { if r >= 0.0 then r else -r }

/* helper modified by LLM (iteration 2): lemma showing symmetry abs(-r) equals abs(r) in conditional form */
lemma abs_symmetry(r: real)
  ensures (if r >= 0.0 then r else -r) == (if -r >= 0.0 then -r else -(-r))
{
  if r >= 0.0 {
  } else {
  }
}
// </vc-helpers>

// <vc-spec>
method fabs(x: seq<real>) returns (result: seq<real>)
  // Ensures the result has the same length as input
  ensures |result| == |x|
  
  // Primary property: each element is the absolute value of the corresponding input element
  ensures forall i :: 0 <= i < |x| ==> result[i] == if x[i] >= 0.0 then x[i] else -x[i]
  
  // Non-negativity: all elements in result are non-negative
  ensures forall i :: 0 <= i < |result| ==> result[i] >= 0.0
  
  // Idempotence: absolute value of the result equals the result itself
  ensures forall i :: 0 <= i < |result| ==> 
    (if result[i] >= 0.0 then result[i] else -result[i]) == result[i]
  
  // Symmetry: abs(x) = abs(-x) for all elements
  ensures forall i :: 0 <= i < |x| ==> 
    result[i] == (if -x[i] >= 0.0 then -x[i] else -(-x[i]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): replaced faulty sequence comprehension with loop and added proof for symmetry */
  var r := x;
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |r| == |x|
    invariant forall j :: 0 <= j < i ==> r[j] == (if x[j] >= 0.0 then x[j] else -x[j])
    invariant forall j :: i < j < |x| ==> r[j] == x[j]
    decreases |x| - i
  {
    var v := if x[i] >= 0.0 then x[i] else -x[i];
    r := r[i := v];
    i := i + 1;
  }
  result := r;

  // Establish symmetry fact to aid prover
  forall k | 0 <= k < |x|
    ensures (if x[k] >= 0.0 then x[k] else -x[k]) == (if -x[k] >= 0.0 then -x[k] else -(-x[k]))
  {
    abs_symmetry(x[k]);
  }
}
// </vc-code>
