//IMPL 

// Question 8 (20 points)
//
// Implement, and have Dafny verify, the method Reverse below, which returns a new array
// aRev consisting of the elements of a, but in reverse order. To create a new 
// array of ints use the Dafny command "new int[...]", where "..." is the number
// of elements in the array.

method Reverse (a : array<int>) returns (aRev : array<int>)
  ensures aRev.Length == a.Length
  ensures forall i : int :: 0 <= i < a.Length ==> a[i] == aRev[aRev.Length-i-1]
  ensures fresh(aRev) // Indicates returned object is newly created in method body
{
  aRev := new int[a.Length];
  var j := 0;
  while j < a.Length
    invariant 0 <= j <= a.Length
    invariant forall k : int :: 0 <= k < j ==> a[k] == aRev[aRev.Length-k-1]
  {
    aRev[aRev.Length-j-1] := a[j];
    j := j + 1;
  }
}