// <vc-preamble>
predicate sorted(a: array?<int>, l: int, u: int)
    reads a
    requires a != null
    {
    forall i, j :: 0 <= l <= i <= j <= u < a.Length ==> a[i] <= a[j]
    }
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method BinarySearch(a: array?<int>, key: int)
    returns (index: int)
    requires a != null && sorted(a,0,a.Length-1);
    ensures index >= 0 ==> index < a.Length && a[index] == key;
    ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key;
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Switched to invariants about where the key is *not* located. */
  if a.Length == 0 {
    index := -1;
    return;
  }

  var low, high := 0, a.Length;
  while low < high
    invariant 0 <= low <= high <= a.Length
    invariant forall k :: 0 <= k < low ==> a[k] != key
    invariant forall k :: high <= k < a.Length ==> a[k] != key
  {
    var mid := low + (high - low) / 2;
    if a[mid] < key {
      low := mid + 1;
    } else if a[mid] > key {
      high := mid;
    } else {
      index := mid;
      return;
    }
  }
  index := -1;
}
// </vc-code>
