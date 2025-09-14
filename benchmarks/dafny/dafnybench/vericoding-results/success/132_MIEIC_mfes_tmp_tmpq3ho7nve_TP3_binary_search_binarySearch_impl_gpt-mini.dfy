// Checks if array 'a' is sorted.
predicate isSorted(a: array<int>)
  reads a
{
    forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

// Finds a value 'x' in a sorted array 'a', and returns its index,
// or -1 if not found.

// Simple test cases to check the post-condition.

/*
a) Identify adequate pre and post-conditions for this method, 
and encode them as “requires” and “ensures” clauses in Dafny. 
You can use the predicate below if needed.

b) Identify an adequate loop variant and loop invariant, and encode them 
as “decreases” and “invariant” clauses in Dafny.
*/

// <vc-helpers>
lemma extend_low(a: array<int>, x: int, mid: int)
  requires isSorted(a)
  requires 0 <= mid < a.Length
  requires a[mid] < x
  ensures forall i {:trigger a[i]} :: 0 <= i < mid+1 ==> a[i] < x
{
  assert forall i {:trigger a[i]} | 0 <= i < mid+1 :: a[i] < x;
}

lemma extend_high(a: array<int>, x: int, mid: int)
  requires isSorted(a)
  requires 0 <= mid < a.Length
  requires a[mid] > x
  ensures forall i {:trigger a[i]} :: mid <= i < a.Length ==> a[i] > x
{
  assert forall i {:trigger a[i]} | mid <= i < a.Length :: a[i] > x;
}
// </vc-helpers>

// <vc-spec>
method binarySearch(a: array<int>, x: int) returns (index: int) 
    requires isSorted(a)
    ensures -1 <= index < a.Length
    ensures if index != -1 then a[index] == x 
        else x !in a[..] //forall i :: 0 <= i < a.Length ==> a[i] != x
// </vc-spec>
// <vc-code>
{
  var low := 0;
  var high := a.Length;
  while low < high
    decreases high - low
    invariant 0 <= low <= high <= a.Length
    invariant forall i :: 0 <= i < low ==> a[i] < x
    invariant forall i :: high <= i < a.Length ==> a[i] > x
  {
    var mid := (low + high) / 2;
    if a[mid] < x {
      extend_low(a, x, mid);
      low := mid + 1;
    } else if a[mid] > x {
      extend_high(a, x, mid);
      high := mid;
    } else {
      index := mid;
      return;
    }
  }
  // After loop, low == high
  assert low == high;
  assert forall i :: 0 <= i < a.Length ==> (if i < low then a[i] < x else a[i] > x);
  assert forall i :: 0 <= i < a.Length ==> a[i] != x;
  index := -1;
  return;
}
// </vc-code>

