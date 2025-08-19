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

//IMPL
method BubbleSort (a: array<int>)
  requires a != null && a.Length > 0; // makes sure a is not empty and length is greater than 0
  modifies a; // as method runs, we are changing a
  ensures sorted(a, 0, a.Length); // makes sure elements of array a are sorted from 0 - a.Length
  ensures multiset(a[..]) == multiset(old(a[..])); // Since a is being modified, we deference the heap 
                           //and compare the previous elements to current elements.
{
  var n := a.Length;
  var i := 0;
  
  while i < n - 1
    /* code modified by LLM (iteration 2): Corrected outer loop invariants - sorted region starts at n-i, not n-1-i */
    invariant 0 <= i <= n - 1
    invariant sorted(a, n - i, n)  // The last i elements are sorted
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant forall x, y :: 0 <= x < n - i && n - i <= y < n ==> a[x] <= a[y]  // Elements before sorted part <= elements in sorted part
  {
    var j := 0;
    while j < n - 1 - i
      /* code modified by LLM (iteration 2): Fixed inner loop invariants to properly track maximum element bubbling */
      invariant 0 <= j <= n - 1 - i
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant sorted(a, n - i, n)  // The sorted part remains sorted
      invariant forall x, y :: 0 <= x < n - i && n - i <= y < n ==> a[x] <= a[y]  // Partition property maintained
      invariant forall k :: 0 <= k < j ==> a[k] <= a[j]  // Maximum element in range [0..j] is at position j
    {
      if a[j] > a[j + 1] {
        a[j], a[j + 1] := a[j + 1], a[j];
      }
      j := j + 1;
    }
    i := i + 1;
  }
}