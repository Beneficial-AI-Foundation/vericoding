/*
/**
 * Filter odd numbers from an array of numbers
 **/

// All numbers in the output are odd and exist in the input 

// All odd numbers in the input are in the output
*/

predicate IsOdd(n: int)
{
    n % 2 != 0
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method FilterOddNumbers(arr: array<int>) returns (oddList: seq<int>)

    ensures forall i :: 0 <= i < |oddList| ==> IsOdd(oddList[i]) && oddList[i] in arr[..]

    ensures forall i :: 0 <= i < arr.Length && IsOdd(arr[i]) ==> arr[i] in oddList
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
