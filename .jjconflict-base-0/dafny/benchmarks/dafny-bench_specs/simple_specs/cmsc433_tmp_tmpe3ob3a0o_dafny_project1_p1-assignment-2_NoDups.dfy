// SPEC

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
}
