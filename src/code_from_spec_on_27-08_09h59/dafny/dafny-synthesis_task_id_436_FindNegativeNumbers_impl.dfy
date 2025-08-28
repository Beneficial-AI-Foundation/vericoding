/**
 * Find negative numbers from an array of numbers
 **/

predicate IsNegative(n: int)
{
    n < 0
}

// <vc-helpers>
lemma SeqContainsElement<T>(s: seq<T>, x: T)
    requires x in s
    ensures exists i :: 0 <= i < |s| && s[i] == x

lemma ArraySliceContains(arr: array<int>, i: int)
    requires 0 <= i < arr.Length
    ensures arr[i] in arr[..]
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method FindNegativeNumbers(arr: array<int>) returns (negativeList: seq<int>)
    // All numbers in the output are negative and exist in the input 
    ensures forall i :: 0 <= i < |negativeList| ==> IsNegative(negativeList[i]) && negativeList[i] in arr[..]
    // All negative numbers in the input are in the output
    ensures forall i :: 0 <= i < arr.Length && IsNegative(arr[i]) ==> arr[i] in negativeList
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    negativeList := [];
    var i := 0;
    
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant forall j :: 0 <= j < |negativeList| ==> IsNegative(negativeList[j]) && negativeList[j] in arr[..]
        invariant forall j :: 0 <= j < i && IsNegative(arr[j]) ==> arr[j] in negativeList
    {
        if IsNegative(arr[i]) {
            ArraySliceContains(arr, i);
            negativeList := negativeList + [arr[i]];
        }
        i := i + 1;
    }
}
// </vc-code>
