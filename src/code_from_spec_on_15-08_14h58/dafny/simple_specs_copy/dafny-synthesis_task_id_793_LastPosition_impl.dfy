//IMPL
method LastPosition(arr: array<int>, elem: int) returns (pos: int)
  requires arr.Length > 0
  requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
  ensures pos == -1 || (0 <= pos < arr.Length && arr[pos] == elem && (pos <= arr.Length - 1 || arr[pos + 1] > elem))
  ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
{
  var left := 0;
  var right := arr.Length - 1;
  pos := -1;
  
  while left <= right
    invariant 0 <= left <= arr.Length
    invariant -1 <= right < arr.Length
    invariant pos == -1 || (0 <= pos < arr.Length && arr[pos] == elem)
    invariant pos == -1 ==> forall i :: 0 <= i < left ==> arr[i] != elem
    invariant pos != -1 ==> pos < left
    invariant forall i :: right < i < arr.Length ==> arr[i] > elem
  {
    var mid := left + (right - left) / 2;
    
    if arr[mid] == elem {
      pos := mid;
      left := mid + 1;
    } else if arr[mid] < elem {
      left := mid + 1;
    } else {
      right := mid - 1;
    }
  }
}