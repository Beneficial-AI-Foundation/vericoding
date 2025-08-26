predicate InsertionSorted(Array: array<int>, left: int, right: int)  
  requires 0 <= left <= right <= Array.Length       
  reads Array       
{           
  forall i,j :: left <= i < j < right ==> Array[i] <= Array[j]
}

// <vc-helpers>
lemma InsertionSortedExtend(Array: array<int>, left: int, right: int)
  requires 0 <= left <= right < Array.Length
  requires InsertionSorted(Array, left, right)
  requires forall k :: left <= k < right ==> Array[k] <= Array[right]
  ensures InsertionSorted(Array, left, right + 1)
{
}

lemma InsertionSortedAfterInsertion(Array: array<int>, pos: int, value: int, i: int)
  requires 0 <= pos < i < Array.Length
  requires Array[pos] == value
  requires forall k :: 0 <= k < pos ==> Array[k] <= value
  requires forall k :: pos + 1 <= k <= i ==> Array[k] >= value
  requires InsertionSorted(Array, 0, pos)
  requires InsertionSorted(Array, pos + 1, i + 1)
  ensures InsertionSorted(Array, 0, i + 1)
{
}

lemma InsertionSortedCombine(Array: array<int>, left: int, mid: int, right: int)
  requires 0 <= left <= mid <= right <= Array.Length
  requires InsertionSorted(Array, left, mid)
  requires InsertionSorted(Array, mid, right)
  requires mid == left || mid == right || Array[mid-1] <= Array[mid]
  ensures InsertionSorted(Array, left, right)
{
}

lemma InsertionSortedAfterShift(Array: array<int>, key: int, j: int, i: int)
  requires 0 <= j + 1 <= i < Array.Length
  requires Array[j + 1] == key
  requires j >= 0 ==> Array[j] <= key
  requires InsertionSorted(Array, 0, j + 1)
  requires forall k :: j + 2 <= k <= i ==> Array[k] >= key
  ensures InsertionSorted(Array, 0, i + 1)
{
}
// </vc-helpers>

// <vc-spec>
method sorting(Array: array<int>)
  requires Array.Length > 1 
  ensures InsertionSorted(Array, 0, Array.Length) 
  modifies Array
// </vc-spec>
// <vc-code>
{
  var i := 1;
  
  while i < Array.Length
    invariant 1 <= i <= Array.Length
    invariant InsertionSorted(Array, 0, i)
  {
    var key := Array[i];
    var j := i - 1;
    
    while j >= 0 && Array[j] > key
      invariant -1 <= j < i
      invariant InsertionSorted(Array, 0, j + 1)
      invariant forall k :: j + 2 <= k <= i ==> 0 <= k < Array.Length && Array[k] >= key
      invariant forall k :: j + 2 <= k <= i ==> Array[k] == old(Array[k])
    {
      Array[j + 1] := Array[j];
      j := j - 1;
    }
    
    Array[j + 1] := key;
    
    // Use the helper lemma to prove insertion maintains sorted property
    InsertionSortedAfterShift(Array, key, j, i);
    
    i := i + 1;
  }
}
// </vc-code>