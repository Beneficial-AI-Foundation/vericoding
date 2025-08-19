//IMPL 
// YOU DO NOT NEED TO IMPLEMENT Euclid!!

// Question 6 (10 points)
//
// Give invariant(s) that enable(s) Dafny to verify the following program, which
// returns true if and only if array a is sorted.

method IsSorted (a : array<int>) returns (isSorted : bool)
  ensures isSorted <==> forall j : int :: 1 <= j < a.Length ==> a[j-1] <= a[j]
{
  if a.Length <= 1 {
    isSorted := true;
    return;
  }
  
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall j : int :: 1 <= j < i ==> a[j-1] <= a[j]
  {
    if a[i-1] > a[i] {
      isSorted := false;
      return;
    }
    i := i + 1;
  }
  isSorted := true;
}