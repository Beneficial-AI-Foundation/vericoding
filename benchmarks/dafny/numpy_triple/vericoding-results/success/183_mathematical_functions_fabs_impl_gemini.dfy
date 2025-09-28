// <vc-preamble>
// Method to compute absolute values element-wise for a sequence of real numbers
// </vc-preamble>

// <vc-helpers>
function abs(r: real): real
  ensures abs(r) >= 0.0
{
  if r >= 0.0 then r else -r
}

/* helper modified by LLM (iteration 4): Kept helper lemma for symmetry of abs */
lemma LemmaAbsSymmetry(r: real)
  ensures abs(r) == abs(-r)
{
  // Dafny can prove this by unfolding the definition of abs.
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
  /* code modified by LLM (iteration 4): used while loop to build sequence, fixing compilation error */
  result := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == abs(x[j])
    invariant forall j :: 0 <= j < i ==> result[j] == abs(-x[j])
  {
    LemmaAbsSymmetry(x[i]);
    result := result + [abs(x[i])];
    i := i + 1;
  }
}
// </vc-code>
