//IMPL 
method LastPosition(arr: array<int>, elem: int) returns (pos: int)
  requires arr.Length > 0
  requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
  ensures pos == -1 || (0 <= pos < arr.Length && arr[pos] == elem && (pos >= arr.Length - 1 || arr[pos + 1] > elem))
  ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
{
  var left := 0;
  var right := arr.Length - 1;
  pos := -1;
  
  while left <= right
    invariant 0 <= left <= arr.Length
    invariant -1 <= right < arr.Length
    invariant pos == -1 || (0 <= pos < arr.Length && arr[pos] == elem)
    invariant forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
    /* code modified by LLM (iteration 1): Updated invariants to properly track the search bounds and found positions */
    invariant forall i :: right < i < arr.Length ==> arr[i] > elem
    invariant forall i :: 0 <= i < left ==> arr[i] < elem || (arr[i] == elem && i <= pos)
    invariant pos != -1 ==> forall i :: pos < i < arr.Length ==> arr[i] > elem || arr[i] == elem
    decreases right - left + 1
  {
    var mid := (left + right) / 2;
    
    if arr[mid] == elem {
      pos := mid;
      left := mid + 1;
    } else if arr[mid] < elem {
      left := mid + 1;
    } else {
      right := mid - 1;
    }
  }
  
  /* code modified by LLM (iteration 1): Added post-loop assertion to help prove the postcondition */
  if pos != -1 {
    assert arr[pos] == elem;
    assert forall i :: pos < i < arr.Length ==> arr[i] > elem;
    if pos < arr.Length - 1 {
      assert arr[pos + 1] > elem;
    }
  }
}