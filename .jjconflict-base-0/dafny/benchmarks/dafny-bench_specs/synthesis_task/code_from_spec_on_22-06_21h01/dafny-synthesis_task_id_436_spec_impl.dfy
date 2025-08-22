/**
 * Find negative numbers from an array of numbers
 **/

// ATOM

predicate IsNegative(n: int)
{
    n < 0
}


// IMPL FindNegativeNumbers

method FindNegativeNumbers(arr: array<int>) returns (negativeList: seq<int>)
    // All numbers in the output are negative and exist in the input 
    ensures forall i :: 0 <= i < |negativeList| ==> IsNegative(negativeList[i]) && negativeList[i] in arr[..]
    // All negative numbers in the input are in the output
    ensures forall i :: 0 <= i < arr.Length && IsNegative(arr[i]) ==> arr[i] in negativeList
{
    negativeList := [];
    var i := 0;
    
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant forall j :: 0 <= j < |negativeList| ==> IsNegative(negativeList[j]) && negativeList[j] in arr[..]
        invariant forall j :: 0 <= j < i && IsNegative(arr[j]) ==> arr[j] in negativeList
    {
        if IsNegative(arr[i]) {
            negativeList := negativeList + [arr[i]];
        }
        i := i + 1;
    }
}