//ATOM swap
method swap(arr: array<int>, i: int, j: int)
  requires arr.Length > 0
  requires 0 <= i < arr.Length && 0 <= j < arr.Length
  modifies arr
  ensures arr[i] == old(arr[j]) && arr[j] == old(arr[i])
  ensures forall k :: 0 <= k < arr.Length && k != i && k != j ==> arr[k] == old(arr[k])
  ensures multiset(arr[..]) == multiset(old(arr[..]))
{
  assume arr[i] == old(arr[j]) && arr[j] == old(arr[i]);
  assume forall k :: 0 <= k < arr.Length && k != i && k != j ==> arr[k] == old(arr[k]);
  assume multiset(arr[..]) == multiset(old(arr[..]));
}

//IMPL MoveZeroesToEnd
method MoveZeroesToEnd(arr: array<int>)
  requires arr.Length >= 2
  modifies arr
  // Same size
  ensures arr.Length == old(arr.Length)
  // Zeros to the right of the first zero
  ensures forall i, j :: 0 <= i < j < arr.Length && arr[i] == 0 ==> arr[j] == 0
  // The final array is a permutation of the original one
  ensures multiset(arr[..]) == multiset(old(arr[..]))
  // Relative order of non-zero elements is preserved
  ensures forall n, m /* on old array */:: 0 <= n < m < arr.Length && old(arr[n]) != 0 && old(arr[m]) != 0 ==> 
      exists k, l /* on new array */:: 0 <= k < l < arr.Length && arr[k] == old(arr[n]) && arr[l] == old(arr[m])
  //ensures IsOrderPreserved(arr[..], old(arr[..]))
  // Number of zeros is preserved
{
  var writePos := 0;
  var oldArr := arr[..];
  var readPos := 0;
  
  /* code modified by LLM (iteration 1): Changed from for loop to while loop and strengthened invariants */
  // First pass: move all non-zero elements to the front
  while readPos < arr.Length
    invariant 0 <= writePos <= readPos <= arr.Length
    invariant forall i :: 0 <= i < writePos ==> arr[i] != 0
    invariant multiset(arr[..]) == multiset(oldArr)
    // Track that non-zero elements maintain relative order
    invariant forall n, m :: 0 <= n < m < readPos && oldArr[n] != 0 && oldArr[m] != 0 ==>
      exists k, l :: 0 <= k < l < writePos && arr[k] == oldArr[n] && arr[l] == oldArr[m]
    // All non-zero elements from processed portion are in the front
    invariant forall i :: 0 <= i < readPos && oldArr[i] != 0 ==> 
      exists j :: 0 <= j < writePos && arr[j] == oldArr[i]
    // Elements in writePos range come from processed portion
    invariant forall i :: 0 <= i < writePos ==> 
      exists j :: 0 <= j < readPos && arr[i] == oldArr[j]
  {
    if arr[readPos] != 0 {
      if readPos != writePos {
        swap(arr, writePos, readPos);
      }
      writePos := writePos + 1;
    }
    readPos := readPos + 1;
  }
  
  /* code modified by LLM (iteration 1): Added second pass to fill remaining positions with zeros */
  // Second pass: fill remaining positions with zeros
  var fillPos := writePos;
  while fillPos < arr.Length
    invariant writePos <= fillPos <= arr.Length
    invariant forall i :: 0 <= i < writePos ==> arr[i] != 0
    invariant forall i :: writePos <= i < fillPos ==> arr[i] == 0
    invariant multiset(arr[..]) == multiset(oldArr)
    // Preserve relative order invariant
    invariant forall n, m :: 0 <= n < m < arr.Length && oldArr[n] != 0 && oldArr[m] != 0 ==>
      exists k, l :: 0 <= k < l < writePos && arr[k] == oldArr[n] && arr[l] == oldArr[m]
  {
    arr[fillPos] := 0;
    fillPos := fillPos + 1;
  }
  
  /* code modified by LLM (iteration 1): Added assertions to help prove the final postconditions */
  // Final assertions to help prove postconditions
  assert forall i :: 0 <= i < writePos ==> arr[i] != 0;
  assert forall i :: writePos <= i < arr.Length ==> arr[i] == 0;
  assert forall i, j :: 0 <= i < j < arr.Length && arr[i] == 0 ==> j >= writePos && arr[j] == 0;
}