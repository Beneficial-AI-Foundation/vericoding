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
//ATOM pivot
predicate pivot(a: array<int>, pivotIndex: int, left: int, right: int)
  requires a != null
  requires 0 <= left <= pivotIndex < right <= a.Length
  reads a
{
  forall k :: left <= k < pivotIndex ==> a[k] <= a[pivotIndex] &&
  forall k :: pivotIndex < k < right ==> a[pivotIndex] <= a[k]
}

// Here having the algorithm for the bubblesort

//IMPL BubbleSort
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
        invariant 0 <= i <= n - 1
        invariant sorted(a, n - 1 - i, n)
        invariant multiset(a[..]) == multiset(old(a[..]))
        /* code modified by LLM (iteration 1): Added invariant to capture that largest elements bubble to the end */
        invariant forall x, y :: 0 <= x < n - 1 - i && n - 1 - i <= y < n ==> a[x] <= a[y]
    {
        var j := 0;
        
        while j < n - 1 - i
            invariant 0 <= j <= n - 1 - i
            invariant multiset(a[..]) == multiset(old(a[..]))
            invariant sorted(a, n - 1 - i, n)
            invariant forall x, y :: 0 <= x < n - 1 - i && n - 1 - i <= y < n ==> a[x] <= a[y]
            /* code modified by LLM (iteration 1): Corrected invariant to track maximum element bubbling up */
            invariant forall k :: 0 <= k <= j ==> a[k] <= a[j]
            /* code modified by LLM (iteration 1): Added invariant ensuring max in range [0,j] reaches position j+1 after each iteration */
            invariant j == 0 || forall k :: 0 <= k < j ==> a[k] <= a[j]
        {
            if a[j] > a[j + 1] {
                a[j], a[j + 1] := a[j + 1], a[j];
            }
            j := j + 1;
        }
        i := i + 1;
    }
}