//ATOM
//Bubblesort CS 494 submission
//References: https://stackoverflow.com/questions/69364687/how-to-prove-time-complexity-of-bubble-sort-using-dafny/69365785#69365785


// predicate checks if elements of a are in ascending order, two additional conditions are added to allow us to sort in specific range within array
predicate sorted(a:array<int>, from:int, to:int)
 reads a
 requires 0 <= from <= to <= a.Length // pre condition checks that from is the start of the range and to is the end of the range, requires values to be within 0 - a.Length
{
 forall x, y :: from <= x < y < to ==> a[x] <= a[y]
}

//IMPL 
// Here having the algorithm for the bubblesort

method BubbleSort (a: array<int>)
  requires a.Length > 0 // makes sure a is not empty and length is greater than 0
  modifies a // as method runs, we are changing a
  ensures sorted(a, 0, a.Length) // makes sure elements of array a are sorted from 0 - a.Length
  ensures multiset(a[..]) == multiset(old(a[..])) // Since a is being modified, we deference the heap 
                           //and compare the previous elements to current elements.
{
  var n := a.Length;
  var i := 0;
  
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant multiset(a[..]) == multiset(old(a[..]))
    /* code modified by LLM (iteration 1): The sorted suffix invariant - elements from n-i to n are sorted */
    invariant forall x, y :: n - i <= x < y < n ==> a[x] <= a[y]
    /* code modified by LLM (iteration 1): Partition invariant - elements in sorted suffix are >= elements before the suffix */
    invariant forall x, y :: 0 <= x < n - i && n - i <= y < n ==> a[x] <= a[y]
  {
    var j := 0;
    
    while j < n - 1 - i
      invariant 0 <= j <= n - 1 - i
      invariant multiset(a[..]) == multiset(old(a[..]))
      /* code modified by LLM (iteration 1): Maintain the sorted suffix from outer loop */
      invariant forall x, y :: n - i <= x < y < n ==> a[x] <= a[y]
      invariant forall x, y :: 0 <= x < n - i && n - i <= y < n ==> a[x] <= a[y]
      /* code modified by LLM (iteration 1): The maximum element found so far is at position j */
      invariant forall k :: 0 <= k <= j ==> a[k] <= a[j]
    {
      if a[j] > a[j + 1] {
        var temp := a[j];
        a[j] := a[j + 1];
        a[j + 1] := temp;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}