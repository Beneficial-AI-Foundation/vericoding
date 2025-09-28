// <vc-preamble>
// Method that computes the element-wise negative of an array of real numbers
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): simple real negation function used in loop */
function Negate(r: real): real { -r }
// </vc-helpers>

// <vc-spec>
method NumpyNegative(x: array<real>) returns (result: array<real>)
  // No preconditions required for negation operation
  ensures result.Length == x.Length  // Result has same length as input
  ensures forall i :: 0 <= i < x.Length ==> result[i] == -x[i]  // Each element is negated
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implement element-wise negation with proper invariants and avoid null comparison warning */
  var n := x.Length;
  result := new real[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result.Length == n
    invariant forall j :: 0 <= j < i ==> result[j] == -x[j]
    decreases n - i
  {
    result[i] := Negate(x[i]);
    i := i + 1;
  }
}
// </vc-code>
