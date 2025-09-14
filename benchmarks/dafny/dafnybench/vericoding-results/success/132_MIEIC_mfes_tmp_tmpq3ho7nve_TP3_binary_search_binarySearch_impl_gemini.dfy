// <vc-preamble>
predicate isSorted(a: array<int>)
  reads a
{
    forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}
// </vc-preamble>

// <vc-helpers>
predicate InBounds(a: array<int>, x: int, low: int, high: int) reads a { forall k :: 0 <= k < a.Length && a[k] == x ==> low <= k < high }
// </vc-helpers>

// <vc-spec>
method binarySearch(a: array<int>, x: int) returns (index: int) 
    requires isSorted(a)
    ensures -1 <= index < a.Length
    ensures if index != -1 then a[index] == x 
        else x !in a[..]
// </vc-spec>
// <vc-code>
{
  var low := 0;
  var high := a.Length;
  while low < high
    invariant 0 <= low <= high <= a.Length
    invariant InBounds(a, x, low, high)
    decreases high - low
  {
    var mid := low + (high - low) / 2;
    if a[mid] < x {
      low := mid + 1;
    } else if a[mid] > x {
      high := mid;
    } else {
      index := mid;
      return;
    }
  }
  index := -1;
}
// </vc-code>
