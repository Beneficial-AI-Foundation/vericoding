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
/* helper modified by LLM (iteration 2): Fixed array type syntax */
lemma ArrayLog1pMonotonic(x: array<real>, result: array<real>)
  requires x.Length == result.Length
  requires forall i :: 0 <= i < x.Length ==> x[i] > -1.0
  requires forall i :: 0 <= i < x.Length ==> result[i] == log(1.0 + x[i])
  ensures forall i, j :: 0 <= i < x.Length && 0 <= j < x.Length && x[i] <= x[j] ==> result[i] <= result[j]
{
  forall i, j | 0 <= i < x.Length && 0 <= j < x.Length && x[i] <= x[j]
    ensures result[i] <= result[j]
  {
    assert 1.0 + x[i] > 0.0;
    assert 1.0 + x[j] > 0.0;
    assert 1.0 + x[i] <= 1.0 + x[j];
    LogMonotonic(1.0 + x[i], 1.0 + x[j]);
  }
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
/* code modified by LLM (iteration 2): Fixed array initialization loop */
{
  result := new real[x.Length];
  for i := 0 to x.Length
    invariant 0 <= i <= x.Length
    invariant forall j :: 0 <= j < i ==> result[j] == log(1.0 + x[j])
    invariant forall j :: 0 <= j < i ==> (x[j] == 0.0 ==> result[j] == 0.0)
  {
    result[i] := log(1.0 + x[i]);
    if x[i] == 0.0 {
      assert result[i] == log(1.0);
      LogOneIsZero();
    }
  }
  ArrayLog1pMonotonic(x, result);
}
// </vc-code>
