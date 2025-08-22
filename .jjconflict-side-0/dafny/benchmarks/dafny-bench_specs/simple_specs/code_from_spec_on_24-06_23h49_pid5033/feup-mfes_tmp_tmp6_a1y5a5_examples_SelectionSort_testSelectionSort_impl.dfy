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
  index := 0;
  assume from <= index < to;
  assume forall k :: from <= k < to ==> a[k] >= a[index];
  return index;
}


//ATOM

// Sorts array 'a' using the selection sort algorithm.
method selectionSort(a: array<real>)
 modifies a
 ensures isSorted(a, 0, a.Length) 
 ensures multiset(a[..]) == multiset(old(a[..]))
{
  assume isSorted(a, 0, a.Length);
  assume multiset(a[..]) ==> multiset(old(a[..]));
}


//IMPL testSelectionSort

method testSelectionSort() {
  /* code modified by LLM (iteration 1): Fixed array initialization using proper Dafny syntax with sequence literal */
  var a := new real[3] [3.0, 1.0, 2.0];
  
  selectionSort(a);
}