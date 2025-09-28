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
/* helper modified by LLM (iteration 4): ensures 1 + x > 0 when x > -1 */
lemma PlusOnePositive(x: real)
  requires x > -1.0
  ensures 1.0 + x > 0.0
{}

/* helper modified by LLM (iteration 4): ensures adding 1 preserves ordering */
lemma AddOneMonotonic(x: real, y: real)
  requires x <= y
  ensures 1.0 + x <= 1.0 + y
{}
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
{
  /* code modified by LLM (iteration 4): implement element-wise log1p and prove postconditions using a forall statement */
  result := new real[x.Length];
  var n := x.Length;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result.Length == n
    invariant forall k :: 0 <= k < i ==> result[k] == log(1.0 + x[k])
    decreases n - i
  {
    assert 0 <= i < x.Length;
    var xi := x[i];
    assert xi > -1.0;
    PlusOnePositive(xi);
    result[i] := log(1.0 + xi);
    i := i + 1;
  }
  assert i == n;

  // Monotonicity proof
  forall ii, jj | 0 <= ii < n && 0 <= jj < n && x[ii] <= x[jj]
    ensures result[ii] <= result[jj]
  {
    assert 0 <= ii < x.Length;
    assert 0 <= jj < x.Length;
    assert x[ii] > -1.0;
    assert x[jj] > -1.0;

    assert 0 <= ii < i;
    assert 0 <= jj < i;

    assert result[ii] == log(1.0 + x[ii]);
    assert result[jj] == log(1.0 + x[jj]);

    PlusOnePositive(x[ii]);
    PlusOnePositive(x[jj]);
    AddOneMonotonic(x[ii], x[jj]);
    LogMonotonic(1.0 + x[ii], 1.0 + x[jj]);
  }
}
// </vc-code>
