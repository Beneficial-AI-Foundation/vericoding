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
lemma SortedPreservation(a: array<int>, from: int, to: int, i: int)
  requires 0 <= from <= i < to <= a.Length
  requires sorted(a, from, i+1)
  requires sorted(a, i, to)
  requires from < i ==> a[i-1] <= a[i]
  ensures sorted(a, from, to)
{
}

method SwapElements(a: array<int>, i: int, j: int)
  requires 0 <= i < j < a.Length
  modifies a
  ensures multiset(a[..]) == multiset(old(a[..]))
  ensures a[i] == old(a[j]) && a[j] == old(a[i])
  ensures forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k])
{
  var temp := a[i];
  a[i] := a[j];
  a[j] := temp;
}

lemma SortedExtension(a: array<int>, from: int, to: int)
  requires 0 <= from < to <= a.Length
  requires sorted(a, from+1, to)
  requires forall k :: from+1 <= k < to ==> a[from] <= a[k]
  ensures sorted(a, from, to)
{
}

lemma BubbleInnerLoopCorrectness(a: array<int>, n: int, i: int)
  requires 0 <= i < n - 1
  requires n == a.Length
  requires forall k :: 0 <= k < n - 1 - i ==> a[k] <= a[k+1]
  ensures forall k :: 0 <= k < n - 1 - i ==> a[k] <= a[n - 1 - i]
{
  if n - 1 - i > 0 {
    var j := 0;
    while j < n - 1 - i
      invariant 0 <= j <= n - 1 - i
      invariant forall k :: 0 <= k <= j ==> a[k] <= a[n - 1 - i]
    {
      j := j + 1;
    }
  }
}

lemma SwapPreservesMultiset(a: array<int>, i: int, j: int)
  requires 0 <= i < a.Length && 0 <= j < a.Length
  modifies a
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var temp := a[i];
  a[i] := a[j];
  a[j] := temp;
}

lemma SortedTransitive(a: array<int>, from: int, mid: int, to: int)
  requires 0 <= from <= mid <= to <= a.Length
  requires sorted(a, from, mid)
  requires sorted(a, mid, to)
  requires from < mid < to ==> a[mid-1] <= a[mid]
  ensures sorted(a, from, to)
{
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
  
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant sorted(a, n - i, n)
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant forall x :: 0 <= x < n - i ==> forall y :: n - i <= y < n ==> a[x] <= a[y]
  {
    var j := 0;
    
    while j < n - 1 - i
      invariant 0 <= j <= n - 1 - i
      invariant sorted(a, n - i, n)
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant forall x :: 0 <= x < n - i ==> forall y :: n - i <= y < n ==> a[x] <= a[y]
      invariant forall k :: 0 <= k < j ==> a[k] <= a[j]
      invariant j < n - 1 - i ==> forall k :: j < k < n - 1 - i ==> a[j] <= a[k+1]
    {
      if a[j] > a[j+1] {
        var temp := a[j];
        a[j] := a[j+1];
        a[j+1] := temp;
      }
      j := j + 1;
    }
    
    assert forall k :: 0 <= k < n - 1 - i ==> a[k] <= a[n - 1 - i];
    i := i + 1;
  }
  
  assert i == n - 1;
  assert sorted(a, 1, n);
  
  if n > 1 {
    assert forall k :: 1 <= k < n ==> a[0] <= a[k];
    SortedExtension(a, 0, n);
  }
}
// </vc-code>

