// <vc-preamble>
// Method that checks if two arrays of real numbers are element-wise equivalent
// </vc-preamble>

// <vc-helpers>

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
  result := true;
  var i := 0;
  while i < a1.Length
    invariant 0 <= i <= a1.Length
    invariant result <==> (forall j :: 0 <= j < i ==> a1[j] == a2[j])
  {
    if a1[i] != a2[i] {
      result := false;
      break;
    }
    i := i + 1;
  }
}
// </vc-code>
