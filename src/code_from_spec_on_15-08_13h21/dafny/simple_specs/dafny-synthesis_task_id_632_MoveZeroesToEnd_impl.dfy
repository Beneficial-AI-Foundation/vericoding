method swap(arr: array<int>, i: int, j: int)
  requires arr.Length > 0
  requires 0 <= i < arr.Length && 0 <= j < arr.Length
  modifies arr
  ensures arr[i] == old(arr[j]) && arr[j] == old(arr[i])
  ensures forall k :: 0 <= k < arr.Length && k != i && k != j ==> arr[k] == old(arr[k])
  ensures multiset(arr[..]) == multiset(old(arr[..]))
{
  var temp := arr[i];
  arr[i] := arr[j];
  arr[j] := temp;
}


//IMPL 
method MoveZeroesToEnd(arr: array<int>)
  requires arr.Length >= 2
  modifies arr
  // Same size
  /* code modified by LLM (iteration 1): removed unnecessary old() wrapper around arr.Length */
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
  ghost var originalArray := arr[..];
  var writeIndex := 0;
  
  // First pass: move all non-zero elements to the front
  for i := 0 to arr.Length
    invariant 0 <= writeIndex <= i <= arr.Length
    invariant forall k :: 0 <= k < writeIndex ==> arr[k] != 0
    invariant multiset(arr[..]) == multiset(originalArray)
    /* code modified by LLM (iteration 1): fixed invariant to only consider processed non-zero elements */
    invariant forall n, m :: 0 <= n < m < i && originalArray[n] != 0 && originalArray[m] != 0 &&
        (exists kn :: 0 <= kn < writeIndex && arr[kn] == originalArray[n]) &&
        (exists km :: 0 <= km < writeIndex && arr[km] == originalArray[m]) ==> 
        exists k, l :: 0 <= k < l < writeIndex && arr[k] == originalArray[n] && arr[l] == originalArray[m]
  {
    if arr[i] != 0 {
      if i != writeIndex {
        swap(arr, i, writeIndex);
      }
      writeIndex := writeIndex + 1;
    }
  }
  
  // Second pass: fill remaining positions with zeros
  for i := writeIndex to arr.Length
    invariant writeIndex <= i <= arr.Length
    invariant forall k :: 0 <= k < writeIndex ==> arr[k] != 0
    invariant forall k :: writeIndex <= k < i ==> arr[k] == 0
    invariant multiset(arr[..]) == multiset(originalArray)
    invariant forall n, m :: 0 <= n < m < arr.Length && originalArray[n] != 0 && originalArray[m] != 0 ==> 
        exists k, l :: 0 <= k < l < writeIndex && arr[k] == originalArray[n] && arr[l] == originalArray[m]
  {
    arr[i] := 0;
  }
}