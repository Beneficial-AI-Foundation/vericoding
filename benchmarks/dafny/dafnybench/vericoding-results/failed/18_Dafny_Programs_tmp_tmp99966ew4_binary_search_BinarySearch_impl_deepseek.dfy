predicate sorted(a: array<int>)
   requires a != null
   reads a
{
   forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}

// <vc-helpers>
predicate sorted(a: array<int>)
   reads a
{
   forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}

lemma BinarySearchLemma(a: array<int>, value: int, low: int, mid: int, high: int)
   requires a != null && sorted(a)
   requires 0 <= low <= mid < high <= a.Length
   requires a[mid] < value
   ensures forall k :: 0 <= k <= mid ==> a[k] != value
{
   forall k | 0 <= k <= mid
      ensures a[k] != value
   {
      if a[k] == value {
         assert a[k] <= a[mid];
         assert a[mid] < value;
      }
   }
}

lemma BinarySearchLemma2(a: array<int>, value: int, low: int, mid: int, high: int)
   requires a != null && sorted(a)
   requires 0 <= low <= mid < high <= a.Length
   requires a[mid] > value
   ensures forall k :: mid <= k < a.Length ==> a[k] != value
{
   forall k | mid <= k < a.Length
      ensures a[k] != value
   {
      if a[k] == value {
         assert a[mid] <= a[k];
         assert value < a[mid];
      }
   }
}
// </vc-helpers>

// <vc-spec>
method BinarySearch(a: array<int>, value: int) returns (index: int)
   requires a != null && 0 <= a.Length && sorted(a)
   ensures 0 <= index ==> index < a.Length && a[index] == value
   ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value
// </vc-spec>
// <vc-code>
{
  var low := 0;
  var high := a.Length;
  index := -1;
  
  while low < high
    invariant 0 <= low <= high <= a.Length
    invariant index == -1
    invariant forall k :: 0 <= k < low ==> a[k] != value
    invariant forall k :: high <= k < a.Length ==> a[k] != value
  {
    var mid := (low + high) / 2;
    
    if a[mid] == value {
      index := mid;
      return;
    } else if a[mid] < value {
      BinarySearchLemma(a, value, low, mid, high);
      low := mid + 1;
    } else {
      BinarySearchLemma2(a, value, low, mid, high);
      high := mid;
    }
  }
}
// </vc-code>

