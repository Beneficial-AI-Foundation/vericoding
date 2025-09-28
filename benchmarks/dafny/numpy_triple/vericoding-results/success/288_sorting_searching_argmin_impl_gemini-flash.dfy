// <vc-preamble>
// Method that returns the index of the minimum value in a non-empty array
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method numpy_argmin(a: array<real>) returns (index: nat)
  // Precondition: array must be non-empty
  requires a.Length > 0
  // Postcondition: returned index is valid
  ensures 0 <= index < a.Length
  // Postcondition: element at returned index is minimum among all elements
  ensures forall j :: 0 <= j < a.Length ==> a[index] <= a[j]
  // Postcondition: for ties, returns the first occurrence (smallest index)
  ensures forall j :: 0 <= j < a.Length && a[j] == a[index] ==> index <= j
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Simplified the condition for updating index to only consider strictly smaller values. This inherently preserves the smallest index for ties and simplifies proof of the 'first occurrence' invariant. */
{
  index := 0;
  var i: nat := 1;
  while i < a.Length
    invariant 0 <= index < i
    invariant 0 < i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[index] <= a[k]
    invariant forall k :: 0 <= k < i && a[k] == a[index] ==> index <= k
  {
    if a[i] < a[index] {
      index := i;
    }
    i := i + 1;
  }
}
// </vc-code>
