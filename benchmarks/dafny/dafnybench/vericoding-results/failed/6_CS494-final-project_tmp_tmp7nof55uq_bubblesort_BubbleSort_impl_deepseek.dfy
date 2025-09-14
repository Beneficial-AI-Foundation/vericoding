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
lemma {:vcs_split_on_every_assert} SwappingPreservesMultiset(a: array<int>, i: int, j: int)
  requires a != null
  requires 0 <= i < a.Length && 0 <= j < a.Length
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var old_arr := old(a[..]);
  var new_arr := a[..];
  assert multiset(new_arr) == multiset(old_arr);
}

lemma {:vcs_split_on_every_assert} BubbleUpPreservesPivot(a: array<int>, to: int, pvt: int)
  requires a != null
  requires 0 <= pvt < to <= a.Length
  requires pivot(a, to, pvt)
  ensures pivot(a, to, pvt)
{
}

lemma {:vcs_split_on_every_assert} BubbleUpIncreasesPivot(a: array<int>, to: int, pvt: int)
  requires a != null
  requires 0 <= pvt < to <= a.Length
  requires pivot(a, to, pvt)
  ensures pvt + 1 < to ==> pivot(a, to, pvt + 1)
{
}

lemma {:vcs_split_on_every_assert} PivotImpliesSorted(a: array<int>, to: int)
  requires a != null
  requires 0 <= to <= a.Length
  requires pivot(a, to, to)
  ensures sorted(a, 0, to)
{
  assert forall x, y :: 0 <= x < y < to ==> a[x] <= a[y];
}

lemma {:vcs_split_on_every_assert} SortedSubrange(a: array<int>, from: int, mid: int, to: int)
  requires a != null
  requires 0 <= from <= mid <= to <= a.Length
  requires sorted(a, from, mid)
  requires sorted(a, mid, to)
  requires forall x, y :: from <= x < mid <= y < to ==> a[x] <= a[y]
  ensures sorted(a, from, to)
{
  assert forall x, y :: from <= x < y < to ==> 
    if y < mid then a[x] <= a[y] 
    else if x >= mid then a[x] <= a[y]
    else a[x] <= a[mid] <= a[y];
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
  var i := a.Length;
  
  while i > 0
    invariant 0 <= i <= a.Length
    invariant sorted(a, i, a.Length)
    invariant multiset(a[..]) == multiset(old(a[..]))
    decreases i
  {
    var j := 0;
    
    while j < i - 1
      invariant 0 <= j <= i - 1
      invariant sorted(a, i, a.Length)
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant forall k :: 0 <= k < j ==> a[k] <= a[j]
      decreases i - j
    {
      if a[j] > a[j + 1] {
        var temp := a[j];
        a[j] := a[j + 1];
        a[j + 1] := temp;
        SwappingPreservesMultiset(a, j, j + 1);
      }
      j := j + 1;
    }
    
    // Prove that the last element is now in its correct position
    assert forall x :: 0 <= x < i - 1 ==> a[x] <= a[i - 1];
    assert sorted(a, i - 1, i);
    
    i := i - 1;
  }
}
// </vc-code>

