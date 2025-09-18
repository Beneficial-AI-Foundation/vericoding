// <vc-preamble>
/*
 * Specification for numpy.argmin - finding the index of the minimum value in an array.
 * This function returns the index of the smallest element, with the first occurrence
 * being returned in case of ties.
 */

// Method to find the index of the minimum element in a non-empty sequence
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ArgMin(a: seq<real>) returns (index: nat)
    // Precondition: array must be non-empty
    requires |a| > 0
    
    // Postcondition: returned index is valid
    ensures 0 <= index < |a|
    
    // Postcondition: element at returned index is minimum among all elements
    ensures forall j :: 0 <= j < |a| ==> a[index] <= a[j]
    
    // Postcondition: returned index is the first occurrence of the minimum value
    ensures forall k :: 0 <= k < index ==> a[k] > a[index]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
