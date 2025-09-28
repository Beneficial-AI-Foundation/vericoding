// <vc-preamble>
// Method that checks if two arrays of real numbers are element-wise equivalent
// </vc-preamble>

// <vc-helpers>
lemma ArrayEquiv_Helper_True(a1: array<real>, a2: array<real>)
  requires a1.Length == a2.Length
  ensures a1.Length == a2.Length
{
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
  var i := 0;
  var ok := true;
  while i < a1.Length
    invariant 0 <= i <= a1.Length
    invariant ok ==> (forall j :: 0 <= j < i ==> a1[j] == a2[j])
    invariant (!ok) ==> (exists j :: 0 <= j < i && a1[j] != a2[j])
  {
    if ok {
      if a1[i] != a2[i] {
        ok := false;
      }
    }
    i := i + 1;
  }
  result := ok;
}

// </vc-code>
