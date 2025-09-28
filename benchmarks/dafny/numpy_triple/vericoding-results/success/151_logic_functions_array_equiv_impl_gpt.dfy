// <vc-preamble>
// Method that checks if two arrays of real numbers are element-wise equivalent
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): define pure function to compare arrays element-wise */
function ArraysEqual(a1: array<real>, a2: array<real>): bool
  requires a1.Length == a2.Length
  reads a1, a2
{
  (forall i :: 0 <= i < a1.Length ==> a1[i] == a2[i])
}
// </vc-helpers>

// <vc-spec>
method ArrayEquiv(a1: array<real>, a2: array<real>) returns (result: bool)
  // Precondition: both arrays must have the same length (shape consistent)
  requires a1.Length == a2.Length
  // Postcondition: result is true iff all corresponding elements are equal
  ensures result <==> (forall i :: 0 <= i < a1.Length ==> a1[i] == a2[i])
  // Additional properties ensured by the specification:
  // - Reflexivity: ArrayEquiv(a, a) always returns true
  // - Symmetry: ArrayEquiv(a, b) == ArrayEquiv(b, a)  
  // - Empty arrays: for length 0, result is vacuously true
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): delegate to pure helper function for element-wise equality */
  result := ArraysEqual(a1, a2);
}
// </vc-code>
