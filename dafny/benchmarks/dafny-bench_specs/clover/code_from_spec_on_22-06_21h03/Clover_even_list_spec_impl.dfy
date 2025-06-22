//IMPL 
method FindEvenNumbers(arr: array<int>) returns (evenNumbers: array<int>)
  ensures forall x :: x in arr[..] && x % 2 == 0 ==> x in evenNumbers[..]
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
  ensures forall k :: 0 <= k < evenNumbers.Length ==> evenNumbers[k] % 2 == 0
  ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
                           exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
{
  var evenList: seq<int> := [];
  ghost var indices: seq<int> := [];

  for i := 0 to arr.Length
    invariant 0 <= i <= arr.Length
    invariant |evenList| == |indices|
    invariant forall j :: 0 <= j < |indices| ==> 0 <= indices[j] < i
    invariant forall j :: 0 <= j < |evenList| ==> evenList[j] % 2 == 0
    invariant forall j :: 0 <= j < |evenList| ==> evenList[j] == arr[indices[j]]
    invariant forall j, k :: 0 <= j < k < |indices| ==> indices[j] < indices[k]
    invariant forall j :: 0 <= j < i && arr[j] % 2 == 0 ==> arr[j] in evenList
    invariant forall x :: x in evenList ==> x in arr[0..i]
  {
    if arr[i] % 2 == 0
    {
      evenList := evenList + [arr[i]];
      indices := indices + [i];
    }
  }

  /* code modified by LLM (iteration 1): Fixed array initialization syntax and added assertions to help verification */
  evenNumbers := new int[|evenList|];
  for i := 0 to |evenList|
    invariant 0 <= i <= |evenList|
    invariant forall j :: 0 <= j < i ==> evenNumbers[j] == evenList[j]
  {
    evenNumbers[i] := evenList[i];
  }
  
  /* code modified by LLM (iteration 1): Added assertions to establish postcondition properties */
  assert forall k :: 0 <= k < evenNumbers.Length ==> evenNumbers[k] in evenList;
  assert forall k :: 0 <= k < evenNumbers.Length ==> evenNumbers[k] in arr[..];
  assert forall x :: x in evenList ==> x in arr[..];
}