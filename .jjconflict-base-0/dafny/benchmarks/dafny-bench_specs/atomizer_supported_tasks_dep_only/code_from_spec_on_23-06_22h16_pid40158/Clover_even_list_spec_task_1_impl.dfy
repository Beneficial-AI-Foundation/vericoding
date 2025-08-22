//IMPL FindEvenNumbers
method FindEvenNumbers (arr: array<int>) returns (evenNumbers: array<int>)
  ensures forall x :: x in arr[..] && (x%2==0) ==> x in evenNumbers[..]
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
  ensures forall k :: 0 <= k < evenNumbers.Length ==> evenNumbers[k] % 2 == 0
  ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
                           exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
{
  var evenList: seq<int> := [];
  ghost var indices: seq<int> := [];

  /* code modified by LLM (iteration 1): fixed loop bounds and strengthened invariants */
  for i := 0 to arr.Length
    invariant 0 <= i <= arr.Length
    invariant |evenList| == |indices|
    invariant forall j :: 0 <= j < |indices| ==> 0 <= indices[j] < arr.Length
    invariant forall j :: 0 <= j < |evenList| ==> evenList[j] % 2 == 0
    invariant forall j :: 0 <= j < |evenList| ==> evenList[j] == arr[indices[j]]
    invariant forall k :: 0 <= k < i && arr[k] % 2 == 0 ==> arr[k] in evenList
    invariant forall j, k :: 0 <= j < k < |indices| ==> indices[j] < indices[k]
    invariant forall j :: 0 <= j < |indices| ==> indices[j] < i
    invariant forall x :: x in evenList ==> x in arr[..]
    invariant forall x :: x !in arr[..] ==> x !in evenList
  {
    if arr[i] % 2 == 0
    {
      evenList := evenList + [arr[i]];
      indices := indices + [i];
    }
  }

  /* code modified by LLM (iteration 1): fixed array initialization syntax */
  evenNumbers := new int[|evenList|];
  for j := 0 to |evenList|
    invariant 0 <= j <= |evenList|
    invariant forall k :: 0 <= k < j ==> evenNumbers[k] == evenList[k]
  {
    evenNumbers[j] := evenList[j];
  }
}