// <vc-preamble>
/*
 * This file implements a specification for creating vectors filled with ones,
 * equivalent to NumPy's ones function for 1D arrays. The function creates
 * a sequence of real numbers where every element is exactly 1.0.
 */

// Method to create a sequence of given length filled with ones
// </vc-preamble>

// <vc-helpers>
function One(): real { 1.0 }
// </vc-helpers>

// <vc-spec>
method ones(n: nat) returns (result: seq<real>)
    // The result has exactly n elements
    ensures |result| == n
    // All elements are exactly 1.0
    ensures forall i :: 0 <= i < |result| ==> result[i] == 1.0
    // All elements are identical (uniformity/constant vector)
    ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result| ==> result[i] == result[j]
    // All elements are positive
    ensures forall i :: 0 <= i < |result| ==> result[i] > 0.0
    // Multiplicative identity property: multiplying any value by an element gives the same value
    ensures forall i :: 0 <= i < |result| ==> forall x {:trigger x * result[i]} :: x * result[i] == x
// </vc-spec>
// <vc-code>
{
  var a := new real[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == One()
  {
    a[i] := One();
    i := i + 1;
  }
  result := a[..];
}
// </vc-code>
