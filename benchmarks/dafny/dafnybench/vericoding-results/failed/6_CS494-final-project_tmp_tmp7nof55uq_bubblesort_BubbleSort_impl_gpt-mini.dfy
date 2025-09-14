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

//helps ensure swapping is valid, it is used inside the nested while loop to make sure linear order is being kept 
predicate pivot(a:array<int>, to:int, pvt:int)
  requires a != null; // requires array to have n amount of elements
  reads a;
  requires 0 <= pvt < to <= a.Length;
{
  forall x, y :: 0 <= x < pvt < y < to ==> a[x] <= a[y] // all values within the array should be in ascending order
}

// Here having the algorithm for the bubblesort

// <vc-helpers>
// helpers cleaned: duplicate predicate definitions removed
// </vc-helpers>

// <vc-spec>
method BubbleSort (a: array<int>)
    requires a != null && a.Length > 0; // makes sure a is not empty and length is greater than 0
    modifies a; // as method runs, we are changing a
    ensures sorted(a, 0, a.Length); // makes sure elements of array a are sorted from 0 - a.Length
    ensures multiset(a[..]) == multiset(old(a[..])); // Since a is being modified, we deference the heap 
                                                      //and compare the previous elements to current elements.
// </vc-spec>
// <vc-code>
{
  ghost var orig := a[..];
  var n := a.Length;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant sorted(a, n - i, n)
    invariant forall x, y :: 0 <= x < n - i <= y < n ==> a[x] <= a[y]
    invariant multiset(a[..]) == multiset(orig)
    decreases n - i
  {
    var j := 1;
    while j < n - i
      invariant 1 <= j <= n - i
      invariant forall t :: 0 <= t < j - 1 ==> a[t] <= a[j - 1]
      invariant forall x, y :: 0 <= x < n - i <= y < n ==> a[x] <= a[y]
      invariant sorted(a, n - i, n)
      invariant multiset(a[..]) == multiset(orig)
      decreases n - i - j
    {
      if a[j - 1] > a[j] {
        var tmp := a[j - 1];
        a[j - 1] := a[j];
        a[j] := tmp;
      }
      j := j + 1;
    }
    ghost var p := n - i - 1;
    assert forall t :: 0 <= t < p ==> a[t] <= a[p];
    assert forall y :: p < y < n ==> a[p] <= a[y];
    assert forall x, y :: n - i <= x < y < n ==> a[x] <= a[y];
    assert sorted(a, p, n);
    i := i + 1;
  }
  assert multiset(a[..]) == multiset(orig);
  assert sorted(a, 0, n);
}
// </vc-code>

