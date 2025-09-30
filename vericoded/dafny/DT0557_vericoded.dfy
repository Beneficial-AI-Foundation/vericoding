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
{
  index := 0;
  var i := 1;
  while i < a.Length
    invariant 0 <= index < i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[index] <= a[j]
    invariant forall j :: 0 <= j < i && a[j] == a[index] ==> index <= j
  {
    if a[i] < a[index] {
      index := i;
    }
    i := i + 1;
  }
}
// </vc-code>
