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
/* code modified by LLM (iteration 3): Fixed the loop invariant regarding `min_val == a[min_idx]` and the postconditions. */
{
  var i := 0;
  var min_val := a[0];
  var min_idx := 0;

  while i < |a|
    invariant 0 <= i <= |a|
    invariant 0 <= min_idx < i || (i == 0 && min_idx == 0)
    invariant min_val == a[min_idx]
    invariant forall k :: 0 <= k < i ==> min_val <= a[k]
    invariant forall k :: 0 <= k < min_idx ==> a[k] > min_val
  {
    if a[i] < min_val {
      min_val := a[i];
      min_idx := i;
    }
    i := i + 1;
  }
  return min_idx;
}
// </vc-code>
