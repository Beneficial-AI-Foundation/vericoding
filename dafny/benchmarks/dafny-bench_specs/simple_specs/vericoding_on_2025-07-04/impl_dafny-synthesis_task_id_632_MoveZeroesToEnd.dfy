//ATOM

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
  assume multiset(arr[..]) == multiset(old(arr[..]))
}

//IMPL
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
  /* code modified by LLM (iteration 1): store original array for tracking */
  var originalArr := arr[..];
  
  var writePos := 0;
  var readPos := 0;
  
  // First pass: move all non-zero elements to the front
  while readPos < arr.Length
    invariant 0 <= writePos <= readPos <= arr.Length
    /* code modified by LLM (iteration 1): all elements before writePos are non-zero */
    invariant forall i :: 0 <= i < writePos ==> arr[i] != 0
    /* code modified by LLM (iteration 1): preserve multiset of entire array */
    invariant multiset(arr[..]) == multiset(originalArr)
    /* code modified by LLM (iteration 1): order preservation for non-zero elements */
    invariant forall n, m :: 0 <= n < m < readPos && originalArr[n] != 0 && originalArr[m] != 0 ==>
        exists k, l :: 0 <= k < l < writePos && arr[k] == originalArr[n] && arr[l] == originalArr[m]
    /* code modified by LLM (iteration 1): track non-zero elements correctly */
    invariant writePos == |seq(readPos, i requires 0 <= i < readPos => if originalArr[i] != 0 then 1 else 0)|
  {
    if arr[readPos] != 0 {
      /* code modified by LLM (iteration 1): move element to write position */
      arr[writePos] := arr[readPos];
      writePos := writePos + 1;
    }
    readPos := readPos + 1;
  }
  
  /* code modified by LLM (iteration 1): fill remaining positions with zeros */
  while writePos < arr.Length
    invariant 0 <= writePos <= arr.Length
    /* code modified by LLM (iteration 1): preserve non-zero elements at front */
    invariant forall i :: 0 <= i < writePos && arr[i] != 0 ==> 
        exists j :: 0 <= j < originalArr.Length && originalArr[j] == arr[i] && originalArr[j] != 0
    /* code modified by LLM (iteration 1): zeros are being filled */
    invariant forall i :: writePos <= i < arr.Length ==> arr[i] == arr[writePos]
  {
    arr[writePos] := 0;
    writePos := writePos + 1;
  }
}