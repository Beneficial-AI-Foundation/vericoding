// Checks if array 'a' is sorted.
predicate isSorted(a: array<int>)
  reads a
{
    forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

// Finds a value 'x' in a sorted array 'a', and returns its index,
// or -1 if not found.

// <vc-helpers>
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
  if a.Length == 0 {
    return -1;
  }
  
  var low := 0;
  var high := a.Length - 1;
  
  while low <= high
    invariant 0 <= low <= a.Length
    invariant -1 <= high < a.Length
    invariant forall i :: 0 <= i < low ==> a[i] < x
    invariant forall i :: high < i < a.Length ==> a[i] > x
    invariant low > high ==> x !in a[..]
    decreases high - low + 1
  {
    var mid := (low + high) / 2;
    
    if a[mid] == x {
      return mid;
    } else if a[mid] < x {
      low := mid + 1;
    } else {
      high := mid - 1;
    }
  }
  
  return -1;
}
// </vc-code>

// Simple test cases to check the post-condition.

/*
a) Identify adequate pre and post-conditions for this method, 
and encode them as "requires" and "ensures" clauses in Dafny. 
You can use the predicate below if needed.

b) Identify an adequate loop variant and loop invariant, and encode them 
as "decreases" and "invariant" clauses in Dafny.
*/