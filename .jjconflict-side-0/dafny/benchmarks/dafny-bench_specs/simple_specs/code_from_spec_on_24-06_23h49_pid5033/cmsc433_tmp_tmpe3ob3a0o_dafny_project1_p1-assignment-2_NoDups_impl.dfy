//IMPL 

// Question 9 (20 points)
//
// Implement and verify method NoDups, which returns true if and only if there
// are no duplicate elements in array a. Note that the requires clause allows
// you to assume that a is sorted, and that this precondition is necessary for
// the ensures clause to imply a lack of duplicates.

method NoDups (a : array<int>) returns (noDups : bool)
  requires forall j : int :: 0 < j < a.Length ==> a[j-1] <= a[j] // a sorted
  ensures noDups <==> forall j : int :: 1 <= j < a.Length ==> a[j-1] != a[j]
{
  if a.Length <= 1 {
    noDups := true;
    return;
  }
  
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall k : int :: 1 <= k < i ==> a[k-1] != a[k]
  {
    if a[i-1] == a[i] {
      noDups := false;
      return;
    }
    i := i + 1;
  }
  noDups := true;
}