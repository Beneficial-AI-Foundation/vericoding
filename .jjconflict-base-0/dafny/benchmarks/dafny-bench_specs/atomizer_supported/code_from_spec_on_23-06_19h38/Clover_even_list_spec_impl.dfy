//IMPL FindEvenNumbers
method FindEvenNumbers(arr: array<int>) returns (evenNumbers: array<int>)
  ensures forall x :: x in arr[..] && x % 2 == 0 ==> x in evenNumbers[..]
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
  ensures forall k :: 0 <= k < evenNumbers.Length ==> evenNumbers[k] % 2 == 0
  ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
                           exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
{
  var evenList: seq<int> := [];
  ghost var indices: seq<int> := [];

  /* code modified by LLM (iteration 1): Fixed loop syntax and enhanced invariants */
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant |evenList| == |indices|
    invariant forall j :: 0 <= j < |indices| ==> 0 <= indices[j] < i
    invariant forall j :: 0 <= j < |evenList| ==> evenList[j] % 2 == 0
    invariant forall j :: 0 <= j < |evenList| ==> evenList[j] == arr[indices[j]]
    invariant forall j, k :: 0 <= j < k < |indices| ==> indices[j] < indices[k]
    invariant forall j :: 0 <= j < i && arr[j] % 2 == 0 ==> arr[j] in evenList
    invariant forall x :: x in evenList ==> x in arr[0..i]
  {
    if arr[i] % 2 == 0 {
      evenList := evenList + [arr[i]];
      indices := indices + [i];
    }
    i := i + 1;
  }

  /* code modified by LLM (iteration 1): Store indices for later use in postcondition verification */
  ghost var finalIndices := indices;

  evenNumbers := new int[|evenList|];
  
  /* code modified by LLM (iteration 1): Fixed loop syntax and enhanced invariants for array copying */
  i := 0;
  while i < |evenList|
    invariant 0 <= i <= |evenList|
    invariant evenNumbers.Length == |evenList|
    invariant forall j :: 0 <= j < i ==> evenNumbers[j] == evenList[j]
    invariant forall j :: 0 <= j < i ==> evenNumbers[j] % 2 == 0
    invariant forall j :: 0 <= j < i ==> evenNumbers[j] in arr[..]
  {
    evenNumbers[i] := evenList[i];
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): Added comprehensive assertions using stored indices */
  assert forall j :: 0 <= j < evenNumbers.Length ==> evenNumbers[j] == evenList[j];
  
  assert forall x :: x in arr[..] && x % 2 == 0 ==> x in evenNumbers[..] by {
    forall x | x in arr[..] && x % 2 == 0 
    ensures x in evenNumbers[..]
    {
      assert x in evenList;
      var idx :| 0 <= idx < |evenList| && evenList[idx] == x;
      assert 0 <= idx < evenNumbers.Length;
      assert evenNumbers[idx] == x;
    }
  }
  
  assert forall x :: x !in arr[..] ==> x !in evenNumbers[..] by {
    forall x | x !in arr[..]
    ensures x !in evenNumbers[..]
    {
      if x in evenNumbers[..] {
        var idx :| 0 <= idx < evenNumbers.Length && evenNumbers[idx] == x;
        assert evenNumbers[idx] == evenList[idx];
        assert evenList[idx] in arr[..];
        assert false;
      }
    }
  }
  
  assert forall k :: 0 <= k < evenNumbers.Length ==> evenNumbers[k] % 2 == 0;
  
  /* code modified by LLM (iteration 1): Use stored finalIndices for order preservation proof */
  assert forall k, l :: 0 <= k < l < evenNumbers.Length ==>
    exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m] by {
    forall k, l | 0 <= k < l < evenNumbers.Length
    ensures exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
    {
      assert evenNumbers[k] == evenList[k];
      assert evenNumbers[l] == evenList[l];
      assert k < |finalIndices| && l < |finalIndices|;
      assert evenList[k] == arr[finalIndices[k]];
      assert evenList[l] == arr[finalIndices[l]];
      assert finalIndices[k] < finalIndices[l];
      var n, m := finalIndices[k], finalIndices[l];
      assert 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m];
    }
  }
}