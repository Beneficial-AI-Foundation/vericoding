// <vc-preamble>
/*
 * Specification for numpy.argmin - finding the index of the minimum value in an array.
 * This function returns the index of the smallest element, with the first occurrence
 * being returned in case of ties.
 */

// Method to find the index of the minimum element in a non-empty sequence
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): [existence of index for non-empty sequence] */
lemma ExistsIndexForNonEmpty(a: seq<real>)
  requires |a| > 0
  ensures 0 <= 0 < |a|
{
}

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
  /* code modified by LLM (iteration 4): [iterative search for first min with invariants] */
  var i := 1;
  index := 0;
  while i < |a|
    invariant 0 <= index < |a|
    invariant 0 <= i <= |a|
    invariant index < i
    invariant forall j :: 0 <= j < i ==> a[index] <= a[j]
    invariant forall k :: 0 <= k < index ==> a[k] > a[index]
    decreases |a| - i
  {
    if a[i] < a[index] {
      index := i;
    }
    i := i + 1;
  }
}

// </vc-code>
