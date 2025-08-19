//ATOM

// Finds the position of a miminum value in non-empty subarray 'a' between positions 
// 'from' (inclusive) and 'to' (exclusive)
method findMin(a: array<real>, from: nat, to: nat) returns(index: nat)
 requires 0 <= from < to <= a.Length
 ensures from <= index < to
 ensures forall k :: from <= k < to ==> a[k] >= a[index]
{
  index := 0;
  assume {:axiom} from <= index < to;
  assume {:axiom} forall k :: from <= k < to ==> a[k] >= a[index];
  return index;
}


//ATOM

// Checks if array 'a' is sorted between positions 'from' (inclusive) and 'to' (exclusive).
predicate isSorted(a: array<real>, from: nat, to: nat)
 requires 0 <= from <= to <= a.Length
 reads a
{
  forall i, j :: from <= i < j < to ==> a[i] <= a[j] 
}


//IMPL selectionSort

// Sorts array 'a' using the selection sort algorithm.
method selectionSort(a: array<real>)
 modifies a
 ensures isSorted(a, 0, a.Length) 
 ensures multiset(a[..]) == multiset(old(a[..]))
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant isSorted(a, 0, i)
    invariant forall x, y :: 0 <= x < i && i <= y < a.Length ==> a[x] <= a[y]
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    if i < a.Length - 1 {
      var minIndex := findMin(a, i, a.Length);
      /* code modified by LLM (iteration 1): store old array content for multiset preservation */
      var oldArray := a[..];
      var temp := a[i];
      a[i] := a[minIndex];
      a[minIndex] := temp;
      
      /* code modified by LLM (iteration 1): assert multiset preservation after swap */
      assert multiset(a[..]) == multiset(oldArray);
      
      /* code modified by LLM (iteration 1): assert sorting properties are maintained */
      assert a[i] <= a[minIndex];
      assert forall k :: i < k < a.Length ==> a[i] <= a[k];
      assert isSorted(a, 0, i+1);
    }
    i := i + 1;
  }
}