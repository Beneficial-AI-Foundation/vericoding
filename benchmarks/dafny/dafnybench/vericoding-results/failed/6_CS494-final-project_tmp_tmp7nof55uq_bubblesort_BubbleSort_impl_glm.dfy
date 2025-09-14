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
predicate sorted(a:array<int>, from:int, to:int)
  requires a != null;
  reads a; 
  requires 0 <= from <= to <= a.Length;
{
  forall x, y :: from <= x < y < to ==> a[x] <= a[y]
}

predicate pivot(a:array<int>, to:int, pvt:int)
  requires a != null;
  reads a;
  requires 0 <= pvt < to <= a.Length;
{
  forall x, y :: 0 <= x < pvt < y < to ==> a[x] <= a[y]
}

lemma swap_preserves_multiset<T>(a: array<T>, i: int, j: int)
  requires a != null && 0 <= i < a.Length && 0 <= j < a.Length
  ensures multiset(a[i := a[j], j := a[i]]) == multiset(a)
{
  var temp := a[i];
  a[i] := a[j];
  a[j] := temp;
  assert multiset(a) == multiset(old(a));
  assert a[i] == old(a[j]);
  assert a[j] == old(a[i]);
  assert multiset(a) == multiset(old(a[..])[i := old(a[j]), j := old(a[i])]);
  assert multiset(old(a[..])[i := old(a[j]), j := old(a[i])]) == multiset(old(a[..]));
}
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
  var n := a.Length;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant sorted(a, 0, i)
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    var j := 0;
    while j < n - i - 1
      invariant 0 <= j <= n - i - 1
      invariant sorted(a, n - i, n)
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant pivot(a, n - i, n - i - 1)
    {
      if a[j] > a[j + 1] {
        a[j], a[j + 1] := a[j + 1], a[j];
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

