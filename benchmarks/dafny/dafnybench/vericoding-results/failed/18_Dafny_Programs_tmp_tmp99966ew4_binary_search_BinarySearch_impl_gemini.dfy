// <vc-preamble>
predicate sorted(a: array<int>)
   requires a != null
   reads a
{
   forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method BinarySearch(a: array<int>, value: int) returns (index: int)
   requires a != null && 0 <= a.Length && sorted(a)
   ensures 0 <= index ==> index < a.Length && a[index] == value
   ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): removed redundant sorted(a) invariant to avoid compiler warnings */
  var low := 0;
  var high := a.Length;
  index := -1;

  while low < high
    invariant 0 <= low <= high <= a.Length
    invariant forall k :: 0 <= k < a.Length && a[k] == value ==> low <= k < high
  {
    var mid := low + (high - low) / 2;
    if a[mid] < value {
      low := mid + 1;
    } else if a[mid] > value {
      high := mid;
    } else {
      index := mid;
      return;
    }
  }
}
// </vc-code>
