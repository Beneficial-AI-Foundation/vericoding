/**
 * Find odd numbers from an array of numbers
 **/

predicate IsOdd(n: int)
{
    n % 2 == 1
}

// <vc-helpers>
lemma OddPreserved(x: int)
    requires IsOdd(x)
    ensures IsOdd(x)
{
}

lemma InArrayPreserved(x: int, arr: array<int>, i: int)
    requires 0 <= i < arr.Length
    requires arr[i] == x
    ensures x in arr[..]
{
}
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
    var i := 0;
    
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant forall j :: 0 <= j < |oddList| ==> IsOdd(oddList[j]) && oddList[j] in arr[..]
        invariant forall j :: 0 <= j < i && IsOdd(arr[j]) ==> arr[j] in oddList
    {
        if IsOdd(arr[i]) {
            oddList := oddList + [arr[i]];
        }
        i := i + 1;
    }
}
// </vc-code>

