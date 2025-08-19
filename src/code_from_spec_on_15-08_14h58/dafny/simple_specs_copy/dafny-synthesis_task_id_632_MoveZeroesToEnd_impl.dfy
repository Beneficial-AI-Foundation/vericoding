method swap(arr: array<int>, i: int, j: int)
  requires arr.Length > 0
  requires 0 <= i < arr.Length && 0 <= j < arr.Length
  modifies arr
  ensures arr[i] == old(arr[j]) && arr[j] == old(arr[i])
  ensures forall k :: 0 <= k < arr.Length && k != i && k != j ==> arr[k] == old(arr[k])
  ensures multiset(arr[..]) == multiset(old(arr[..]))
{
  /* code modified by LLM (iteration 2): implement actual swap instead of assume statements */
  var temp := arr[i];
  arr[i] := arr[j];
  arr[j] := temp;
}


//IMPL 
method MoveZeroesToEnd(arr: array<int>)
  requires arr.Length >= 2
  modifies arr
  // Same size
  /* code modified by LLM (iteration 2): removed old() wrapper as arr.Length is immutable */
  ensures arr.Length == old(arr).Length
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
  ghost var oldArr := arr[..];
  
  // First pass: move all non-zero elements to the front
  for readPos := 0 to arr.Length
    invariant 0 <= writePos <= readPos <= arr.Length
    invariant forall i :: 0 <= i < writePos ==> arr[i] != 0
    /* code modified by LLM (iteration 2): maintain multiset property */
    invariant multiset(arr[..]) == multiset(oldArr)
    /* code modified by LLM (iteration 2): corrected order preservation invariant - only consider elements that have been moved to writePos */
    invariant forall n, m :: 0 <= n < m < readPos && oldArr[n] != 0 && oldArr[m] != 0 ==>
        exists k, l :: 0 <= k < l < writePos && arr[k] == oldArr[n] && arr[l] == oldArr[m] && 
        (exists p :: 0 <= p < readPos && oldArr[p] == arr[k] && p <= n) &&
        (exists q :: 0 <= q < readPos && oldArr[q] == arr[l] && q <= m)
    /* code modified by LLM (iteration 2): all non-zero elements processed are moved to front in order */
    invariant forall i :: 0 <= i < readPos && oldArr[i] != 0 ==> 
        exists j :: 0 <= j < writePos && arr[j] == oldArr[i]
    /* code modified by LLM (iteration 2): writePos counts exactly the non-zero elements seen so far */
    invariant writePos == |set i | 0 <= i < readPos && oldArr[i] != 0|
  {
    if arr[readPos] != 0 {
      if readPos != writePos {
        /* code modified by LLM (iteration 2): use swap to maintain multiset property */
        swap(arr, readPos, writePos);
      }
      writePos := writePos + 1;
    }
  }
  
  // Second pass: fill remaining positions with zeros
  /* code modified by LLM (iteration 2): count zeros to maintain multiset property */
  ghost var zerosInOriginal := |set i | 0 <= i < arr.Length && oldArr[i] == 0|;
  ghost var zerosNeeded := arr.Length - writePos;
  
  for i := writePos to arr.Length
    invariant writePos <= i <= arr.Length
    invariant forall j :: 0 <= j < writePos ==> arr[j] != 0
    invariant forall j :: writePos <= j < i ==> arr[j] == 0
    /* code modified by LLM (iteration 3): fix compilation errors - corrected multiset invariant */
    invariant zerosInOriginal == zerosNeeded
    invariant multiset(arr[0..writePos]) == multiset(seq(writePos, k requires 0 <= k < writePos => if 0 <= k < |oldArr| && oldArr[k] != 0 then oldArr[k] else 0))
    /* code modified by LLM (iteration 3): simplified length invariant to avoid type errors */
    invariant (i - writePos) + writePos + (arr.Length - i) == arr.Length
  {
    /* code modified by LLM (iteration 2): only assign zero if current value is not zero to maintain multiset */
    if arr[i] != 0 {
      arr[i] := 0;
    }
  }
}