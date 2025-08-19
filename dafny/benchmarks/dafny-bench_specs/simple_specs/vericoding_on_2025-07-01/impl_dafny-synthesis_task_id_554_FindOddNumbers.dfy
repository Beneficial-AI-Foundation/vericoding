//ATOM

predicate IsOdd(n: int)
{
  n % 2 == 1
}


// SPEC

method FindOddNumbers(arr: array<int>) returns (oddList: seq<int>)
  // All numbers in the output are odd and exist in the input 
  ensures forall i :: 0 <= i < |oddList| ==> IsOdd(oddList[i]) && oddList[i] in arr[..]
  // All odd numbers in the input are in the output
  ensures forall i :: 0 <= i < arr.Length && IsOdd(arr[i]) ==> arr[i] in oddList
{
}