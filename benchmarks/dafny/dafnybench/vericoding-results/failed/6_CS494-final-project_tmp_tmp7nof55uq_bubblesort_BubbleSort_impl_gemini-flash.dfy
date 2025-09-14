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
lemma {:induction false} SwapLemma(a: array<int>, i: int, j: int)
  requires a != null;
  requires 0 <= i < a.Length;
  requires 0 <= j < a.Length;
  modifies a;
  ensures a[i] == old(a[j]);
  ensures a[j] == old(a[i]);
  ensures forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k]);
{
  var temp := a[i];
  a[i], a[j] := a[j], temp;
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
    var N := a.Length;
    if N == 0 || N == 1 {
        return;
    }

    for i := 0 to N - 2
        invariant 0 <= i < N;
        invariant sorted(a, N - i, N);
        invariant forall k :: 0 <= k < N - i ==> a[k] <= a[N - i];
        invariant multiset(a[..]) == multiset(old(a[..]));
    {
        for j := 0 to N - 2 - i
            invariant 0 <= j <= N - 1 - i;
            invariant sorted(a, N - i, N);
            invariant multiset(a[..]) == multiset(old(a[..]));
            invariant forall k :: 0 <= k < j ==> a[k] <= a[j];
            invariant forall k :: j < k < N - i ==> a[j] <= a[k];
            invariant forall k :: N - i <= k < N ==> (old(a)[k] == a[k]);
        {
            if a[j] > a[j+1] {
                SwapLemma(a, j, j+1);
            }
        }
        assert sorted(a, N - 1 - i, N);
        assert forall k :: 0 <= k < N - 1 - i ==> a[k] <= a[N - 1 - i];
    }
}
// </vc-code>

