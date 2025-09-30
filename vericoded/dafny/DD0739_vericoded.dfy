/**
 * Find odd numbers from an array of numbers
 **/

predicate IsOdd(n: int)
{
    n % 2 == 1
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method FindOddNumbers(arr: array<int>) returns (oddList: seq<int>)
    // All numbers in the output are odd and exist in the input 
    ensures forall i :: 0 <= i < |oddList| ==> IsOdd(oddList[i]) && oddList[i] in arr[..]
    // All odd numbers in the input are in the output
    ensures forall i :: 0 <= i < arr.Length && IsOdd(arr[i]) ==> arr[i] in oddList
// </vc-spec>
// <vc-code>
{
    oddList := [];
    for i := 0 to arr.Length
        invariant 0 <= i <= arr.Length
        invariant forall j :: 0 <= j < |oddList| ==> IsOdd(oddList[j]) && oddList[j] in arr[..]
        invariant forall j :: 0 <= j < i && IsOdd(arr[j]) ==> arr[j] in oddList
    {
        if IsOdd(arr[i]) {
            oddList := oddList + [arr[i]];
        }
    }
}
// </vc-code>

