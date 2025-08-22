/**
 * Filter odd numbers from an array of numbers
 **/

// ATOM

predicate IsOdd(n: int)
{
    n % 2 != 0
}

// IMPL

method FilterOddNumbers(arr: array<int>) returns (oddList: seq<int>)
    // All numbers in the output are odd and exist in the input 
    ensures forall i :: 0 <= i < |oddList| ==> IsOdd(oddList[i]) && oddList[i] in arr[..]
    // All odd numbers in the input are in the output
    ensures forall i :: 0 <= i < arr.Length && IsOdd(arr[i]) ==> arr[i] in oddList
{
    oddList := [];
    var index := 0;
    
    while index < arr.Length
        invariant 0 <= index <= arr.Length
        invariant forall i :: 0 <= i < |oddList| ==> IsOdd(oddList[i]) && oddList[i] in arr[..]
        invariant forall i :: 0 <= i < index && IsOdd(arr[i]) ==> arr[i] in oddList
    {
        if IsOdd(arr[index]) {
            oddList := oddList + [arr[index]];
        }
        index := index + 1;
    }
}