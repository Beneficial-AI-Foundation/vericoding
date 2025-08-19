// predicate checks if elements of a are in ascending order, two additional conditions are added to allow us to sort in specific range within array
predicate sorted(a:array<int>, from:int, to:int)
 reads a 
 requires 0 <= from <= to <= a.Length // pre condition checks that from is the start of the range and to is the end of the range, requires values to be within 0 - a.Length
{
 forall x, y :: from <= x < y < to ==> a[x] <= a[y]
}

//IMPL BubbleSort
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
    /* code modified by LLM (iteration 1): Added proper invariants for bubble sort outer loop */
    invariant 0 <= i <= n - 1
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant sorted(a, n - i, n)
    invariant forall k, l :: 0 <= k < n - i && n - i <= l < n ==> a[k] <= a[l]
  {
    var j := 0;
    
    while j < n - 1 - i
      /* code modified by LLM (iteration 1): Fixed invariants for bubble sort inner loop */
      invariant 0 <= j <= n - 1 - i
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant sorted(a, n - i, n)
      invariant forall k, l :: 0 <= k < n - i && n - i <= l < n ==> a[k] <= a[l]
      invariant forall k :: 0 <= k < j ==> a[k] <= a[j]
    {
      if a[j] > a[j + 1] {
        a[j], a[j + 1] := a[j + 1], a[j];
      }
      j := j + 1;
    }
    i := i + 1;
  }
}