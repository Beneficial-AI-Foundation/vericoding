/*
/**
 * Remove odd numbers from an array of numbers
 **/

// All numbers in the output are even and exist in the input 

// All even numbers in the input are in the output
*/

predicate IsEven(n: int)
{
    n % 2 == 0
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method RemoveOddNumbers(arr: array<int>) returns (evenList: seq<int>)

    ensures forall i :: 0 <= i < |evenList| ==> IsEven(evenList[i]) && evenList[i] in arr[..]

    ensures forall i :: 0 <= i < arr.Length && IsEven(arr[i]) ==> arr[i] in evenList
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
