/**
 * Remove odd numbers from an array of numbers
 **/

predicate IsEven(n: int)
{
    n % 2 == 0
}

// <vc-helpers>
// Possibly add lemmas, predicates, or invariants if needed, but currently empty as the implementation below self-contains.
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
  var temp := [];
  for i := 0 to arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall k :: 0 <= k < |temp| ==> IsEven(temp[k]) && temp[k] in arr[..]
    invariant forall x :: x in temp ==> exists j :: 0 <= j < i && arr[j] == x && IsEven(arr[j])
    invariant forall j :: 0 <= j < i && IsEven(arr[j]) ==> arr[j] in temp
  {
    if IsEven(arr[i]) {
      temp := temp + [arr[i]];
    }
  }
  evenList := temp;
}
// </vc-code>

