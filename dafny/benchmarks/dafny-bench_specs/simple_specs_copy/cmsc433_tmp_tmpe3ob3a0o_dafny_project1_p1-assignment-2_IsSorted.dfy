// SPEC
  

  // YOU DO NOT NEED TO IMPLEMENT Euclid!!

// Question 6 (10 points)
//
// Give invariant(s) that enable(s) Dafny to verify the following program, which
// returns true if and only if array a is sorted.

method IsSorted (a : array<int>) returns (isSorted : bool)
  ensures isSorted <==> forall j : int :: 1 <= j < a.Length ==> a[j-1] <= a[j]
{
}
