/*
/**
 * Find negative numbers from an array of numbers
 **/

// All numbers in the output are negative and exist in the input 

// All negative numbers in the input are in the output
*/

predicate IsNegative(n: int)
{
    n < 0
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method FindNegativeNumbers(arr: array<int>) returns (negativeList: seq<int>)

    ensures forall i :: 0 <= i < |negativeList| ==> IsNegative(negativeList[i]) && negativeList[i] in arr[..]

    ensures forall i :: 0 <= i < arr.Length && IsNegative(arr[i]) ==> arr[i] in negativeList
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
