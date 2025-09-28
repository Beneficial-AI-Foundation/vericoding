// <vc-preamble>
// Method that checks if two arrays of real numbers are element-wise equivalent
// </vc-preamble>

// <vc-helpers>
lemma ArrayEquivLemma(a1: array<real>, a2: array<real>, i: int)
  requires a1.Length == a2.Length
  requires 0 <= i <= a1.Length
  ensures (forall j :: 0 <= j < i ==> a1[j] == a2[j]) ==> (i == a1.Length ==> (forall j :: 0 <= j < a1.Length ==> a1[j] == a2[j]))
  decreases a1.Length - i
{
  if i < a1.Length {
    // Continue checking
    ArrayEquivLemma(a1, a2, i + 1);
  }
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
  /* code modified by LLM (iteration 2): Added termination clause to lemma call */
  if a1.Length == 0 {
    result := true;
    return;
  }
  
  var index := 0;
  result := true;
  
  while index < a1.Length
    invariant 0 <= index <= a1.Length
    invariant result <==> (forall j :: 0 <= j < index ==> a1[j] == a2[j])
  {
    if a1[index] != a2[index] {
      result := false;
      return;
    }
    index := index + 1;
  }
  
  ArrayEquivLemma(a1, a2, a1.Length);
}
// </vc-code>
