//ATOM
//Bubblesort CS 494 submission
//References: https://stackoverflow.com/questions/69364687/how-to-prove-time-complexity-of-bubble-sort-using-dafny/69365785#69365785


// predicate checks if elements of a are in ascending order, two additional conditions are added to allow us to sort in specific range within array
predicate sorted(a:array<int>, from:int, to:int)
 requires a != null; // requires array to have n amount of elements
 reads a; 
 requires 0 <= from <= to <= a.Length; // pre condition checks that from is the start of the range and to is the end of the range, requires values to be within 0 - a.Length
{
 forall x, y :: from <= x < y < to ==> a[x] <= a[y]
}


// SPEC

// Here having the algorithm for the bubblesort

method BubbleSort (a: array<int>)
  requires a != null && a.Length > 0; // makes sure a is not empty and length is greater than 0
  modifies a; // as method runs, we are changing a
  ensures sorted(a, 0, a.Length); // makes sure elements of array a are sorted from 0 - a.Length
  ensures multiset(a[..]) == multiset(old(a[..])); // Since a is being modified, we deference the heap 
                           //and compare the previous elements to current elements.
{
}
