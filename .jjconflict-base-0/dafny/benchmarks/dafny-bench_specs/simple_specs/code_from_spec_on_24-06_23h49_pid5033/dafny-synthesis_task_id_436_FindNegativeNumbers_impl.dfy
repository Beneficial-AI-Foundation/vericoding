//ATOM
predicate IsNegative(n: int)
{
  n < 0
}

//IMPL FindNegativeNumbers
method FindNegativeNumbers(arr: array<int>) returns (negativeList: seq<int>)
  // All numbers in the output are negative and exist in the input 
  ensures forall i :: 0 <= i < |negativeList| ==> IsNegative(negativeList[i]) && negativeList[i] in arr[..]
  // All negative numbers in the input are in the output
  ensures forall i :: 0 <= i < arr.Length && IsNegative(arr[i]) ==> arr[i] in negativeList
{
  negativeList := [];
  var index := 0;
  
  while index < arr.Length
    invariant 0 <= index <= arr.Length
    invariant forall i :: 0 <= i < |negativeList| ==> IsNegative(negativeList[i]) && negativeList[i] in arr[..]
    invariant forall i :: 0 <= i < index && IsNegative(arr[i]) ==> arr[i] in negativeList
  {
    if IsNegative(arr[index]) {
      negativeList := negativeList + [arr[index]];
    }
    index := index + 1;
  }
}