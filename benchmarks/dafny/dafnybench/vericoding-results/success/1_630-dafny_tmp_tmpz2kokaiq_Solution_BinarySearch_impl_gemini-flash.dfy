function sorted(a: array<int>) : bool
    reads a
{
   forall i,j : int :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

// <vc-helpers>
lemma lemma_sorted_range(a: array<int>, low: int, high: int)
  requires sorted(a)
  requires 0 <= low <= high < a.Length
  ensures forall i, j :: low <= i < j <= high ==> a[i] <= a[j]
{
  // This is directly implied by the definition of sorted,
  // but sometimes Dafny needs help with quantifiers over sub-ranges.
}
// </vc-helpers>

// <vc-spec>
method BinarySearch(a: array<int>, x: int) returns (index: int)
    requires sorted(a)
    ensures 0 <= index < a.Length ==> a[index] == x
    ensures index == -1 ==> forall i : int :: 0 <= i < a.Length ==> a[i] != x
// </vc-spec>
// <vc-code>
{
  var low := 0;
  var high := a.Length;
  var resultIndex := -1; // Renamed to avoid duplication

  while low < high
    invariant 0 <= low <= high <= a.Length
    invariant resultIndex == -1 // resultIndex is only updated if found
    invariant forall k :: 0 <= k < low ==> a[k] != x // x is not in the left search space
    invariant forall k :: high <= k < a.Length ==> a[k] != x // x is not in the right search space
    invariant sorted(a) // The array remains sorted
  {
    var mid := low + (high - low) / 2;
    // assert low <= mid < high; // This is a useful assertion to think about

    if a[mid] == x {
      resultIndex := mid;
      return resultIndex; // Found the element, return its index
    } else if a[mid] < x {
      low := mid + 1;
    } else { // a[mid] > x
      high := mid;
    }
  }

  // After the loop, low >= high.
  // The loop invariant states that x is not in 0..low-1 and not in high..a.Length-1.
  // Given low >= high, this implies x is not in 0..a.Length-1.
  return resultIndex; // If loop finishes, x was not found, so return -1
}
// </vc-code>

