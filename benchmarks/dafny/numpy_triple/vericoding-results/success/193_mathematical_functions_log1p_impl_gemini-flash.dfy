// <vc-preamble>
/*
 * log1p function: Return the natural logarithm of one plus the input array, element-wise.
 * Calculates log(1 + x) for each element, providing greater precision than naive log(1 + x) 
 * computation for small values near zero.
 */

// Uninterpreted function representing natural logarithm
function log(x: real): real
  requires x > 0.0
{
  // Placeholder implementation for compilation - actual behavior defined by axioms
  0.0
}

// Axiom: log(1) = 0
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed unnecessary requires clauses as they are already asserted in body of lemma */
lemma helper_LogMonotonicExt(x_orig: real, y_orig: real, x_shifted: real, y_shifted: real)
  requires x_orig > -1.0 && y_orig > -1.0
  requires x_shifted == 1.0 + x_orig
  requires y_shifted == 1.0 + y_orig
  // Need to prove that x_shifted <= y_shifted (from x_orig <= y_orig)
  // and that both x_shifted and y_shifted are > 0.0
  requires x_orig <= y_orig
  ensures log(x_shifted) <= log(y_shifted)
{
  assert x_shifted > 0.0;
  assert y_shifted > 0.0;
  LogMonotonic(x_shifted, y_shifted);
}
// </vc-helpers>

// <vc-spec>
lemma {:axiom} LogOneIsZero()
  ensures log(1.0) == 0.0

// Axiom: log is strictly increasing
lemma {:axiom} LogMonotonic(x: real, y: real)
  requires x > 0.0 && y > 0.0
  requires x <= y
  ensures log(x) <= log(y)

// Method that computes log1p for each element in the input array
method log1p(x: array<real>) returns (result: array<real>)
  // Precondition: All elements must be greater than -1
  requires forall i :: 0 <= i < x.Length ==> x[i] > -1.0
  
  // Postcondition: Result has same length as input
  ensures result.Length == x.Length
  
  // Postcondition: Each element is log(1 + x[i])
  ensures forall i :: 0 <= i < x.Length ==> result[i] == log(1.0 + x[i])
  
  // Postcondition: log1p(0) = 0 (follows from log(1) = 0)
  ensures forall i :: 0 <= i < x.Length ==> (x[i] == 0.0 ==> result[i] == 0.0)
  
  // Postcondition: log1p is monotonic (preserves ordering)
  ensures forall i, j :: 0 <= i < x.Length && 0 <= j < x.Length && x[i] <= x[j] ==> result[i] <= result[j]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added additional assertion in loop to verify that x[k] <= x[i] which satisfies the precondition for the helper_LogMonotonicExt lemma. Added an additional ensures clause in forall loop */
{
  result := new real[x.Length];
  var i := 0;
  while i < x.Length
    invariant 0 <= i <= x.Length
    invariant result.Length == x.Length
    invariant forall k :: 0 <= k < i ==> result[k] == log(1.0 + x[k])
    invariant forall k :: 0 <= k < i ==> (x[k] == 0.0 ==> result[k] == 0.0)
    invariant forall k, l :: 0 <= k < i && 0 <= l < i && x[k] <= x[l] ==> result[k] <= result[l]
  {
    var operand := 1.0 + x[i];
    result[i] := log(operand);

    // Postcondition for x[i] == 0.0
    if x[i] == 0.0 {
      assert operand == 1.0;
      LogOneIsZero();
      assert result[i] == 0.0;
    }

    // Postcondition for monotonicity of already processed elements
    forall k | 0 <= k < i
      ensures x[k] <= x[i] ==> result[k] <= result[i]
    {
      // We need to show log(1.0 + x[k]) <= log(1.0 + x[i])
      // given x[k] <= x[i]
      if (x[k] <= x[i]) {
        helper_LogMonotonicExt(x[k], x[i], 1.0 + x[k], 1.0 + x[i]);
      }
    }
    
    // Postcondition for monotonicity of already processed elements in reverse
    forall k | 0 <= k < i
      ensures x[i] <= x[k] ==> result[i] <= result[k]
    {
      if (x[i] <= x[k]) {
        helper_LogMonotonicExt(x[i], x[k], 1.0 + x[i], 1.0 + x[k]);
      }
    }

    i := i + 1;
  }
}
// </vc-code>
