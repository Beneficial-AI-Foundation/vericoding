//ATOM

// Checks if array 'a' is sorted between positions 'from' (inclusive) and 'to' (exclusive).
predicate isSorted(a: array<real>, from: nat, to: nat)
 requires 0 <= from <= to <= a.Length
 reads a
{
  forall i, j :: from <= i < j < to ==> a[i] <= a[j] 
}


//ATOM

// Finds the position of a miminum value in non-empty subarray 'a' between positions 
// 'from' (inclusive) and 'to' (exclusive)
method findMin(a: array<real>, from: nat, to: nat) returns(index: nat)
 requires 0 <= from < to <= a.Length
 ensures from <= index < to
 ensures forall k :: from <= k < to ==> a[k] >= a[index]
{
  /* code modified by LLM (iteration 1): Fixed implementation to properly find minimum index */
  index := from;
  var i := from + 1;
  while i < to
    invariant from <= index < to
    invariant from + 1 <= i <= to
    invariant forall k :: from <= k < i ==> a[k] >= a[index]
  {
    if a[i] < a[index] {
      index := i;
    }
    i := i + 1;
  }
}


//ATOM

// Sorts array 'a' using the selection sort algorithm.
method selectionSort(a: array<real>)
 modifies a
 ensures isSorted(a, 0, a.Length) 
 ensures multiset(a[..]) == multiset(old(a[..]))
{
  /* code modified by LLM (iteration 1): Fixed syntax error and implemented selection sort */
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant isSorted(a, 0, i)
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant forall x, y :: 0 <= x < i <= y < a.Length ==> a[x] <= a[y]
  {
    var minIndex := findMin(a, i, a.Length);
    a[i], a[minIndex] := a[minIndex], a[i];
    i := i + 1;
  }
}


//IMPL 

/* code modified by LLM (iteration 1): Simple test method implementation */
method testSelectionSort() {
  var a := new real[3];
  a[0] := 3.0;
  a[1] := 1.0;
  a[2] := 2.0;
  selectionSort(a);
}