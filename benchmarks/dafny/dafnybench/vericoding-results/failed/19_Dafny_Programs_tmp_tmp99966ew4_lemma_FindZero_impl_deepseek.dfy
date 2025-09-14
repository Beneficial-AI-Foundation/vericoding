

// <vc-helpers>
lemma BinarySearchZero(a: array<int>, low: int, high: int) returns (index: int)
  requires a != null
  requires 0 <= low <= high < a.Length
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
  ensures low <= index <= high
  ensures index < high ==> a[index] == 0
  ensures index == high ==> a[high] != 0
{
  if low == high {
    index := high;
  } else {
    var mid := low + (high - low) / 2;
    if a[mid] == 0 {
      index := mid;
    } else if a[mid] > mid {
      index := BinarySearchZero(a, low, mid);
    } else {
      index := BinarySearchZero(a, mid + 1, high);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method FindZero(a: array<int>) returns (index: int)
   requires a != null
   requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
   requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
   ensures index < 0  ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
   ensures 0 <= index ==> index < a.Length && a[index] == 0
// </vc-spec>
// <vc-code>
{
  if a.Length == 0 {
    index := -1;
  } else if a[0] == 0 {
    index := 0;
  } else {
    var ghost_index := BinarySearchZero(a, 0, a.Length - 1);
    if a[ghost_index] != 0 {
      index := -1;
    } else {
      index := ghost_index;
    }
  }
}
// </vc-code>

