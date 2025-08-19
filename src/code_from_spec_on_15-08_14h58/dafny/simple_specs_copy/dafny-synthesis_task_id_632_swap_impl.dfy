//IMPL 

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