/**
 * Remove odd numbers from an array of numbers
 **/

predicate IsEven(n: int)
{
    n % 2 == 0
}

// <vc-helpers>
lemma EvenInEvenList(evenList: seq<int>, arr_i: int) 
  requires arr_i in evenList
  requires forall i :: 0 <= i < |evenList| ==> IsEven(evenList[i])
  ensures IsEven(arr_i)
{
}
// </vc-helpers>

// <vc-spec>
method RemoveOddNumbers(arr: array<int>) returns (evenList: seq<int>)
    // All numbers in the output are even and exist in the input 
    ensures forall i :: 0 <= i < |evenList| ==> IsEven(evenList[i]) && evenList[i] in arr[..]
    // All even numbers in the input are in the output
    ensures forall i :: 0 <= i < arr.Length && IsEven(arr[i]) ==> arr[i] in evenList
// </vc-spec>
// <vc-code>
{
  var evenList_local: seq<int> := [];
  for i := 0 to arr.Length 
    invariant 0 <= i <= arr.Length
    invariant forall k :: 0 <= k < |evenList_local| ==> IsEven(evenList_local[k]) && evenList_local[k] in arr[..]
    invariant forall k :: 0 <= k < i && IsEven(arr[k]) ==> arr[k] in evenList_local
  {
    if i < arr.Length && IsEven(arr[i])
    {
      evenList_local := evenList_local + [arr[i]];
    }
  }
  return evenList_local;
}
// </vc-code>

