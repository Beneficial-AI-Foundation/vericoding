// <vc-preamble>
// Method that checks if two arrays of real numbers are element-wise equivalent
// </vc-preamble>

// <vc-helpers>
lemma helper_reflexivity(a: array<real>) 
  ensures forall i :: 0 <= i < a.Length ==> a[i] == a[i] 
{}
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
  result := true;
  while i < a1.Length
    invariant 0 <= i <= a1.Length
    invariant result <==> (forall k :: 0 <= k < i ==> a1[k] == a2[k])
  {
    if a1[i] != a2[i] {
      result := false;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
