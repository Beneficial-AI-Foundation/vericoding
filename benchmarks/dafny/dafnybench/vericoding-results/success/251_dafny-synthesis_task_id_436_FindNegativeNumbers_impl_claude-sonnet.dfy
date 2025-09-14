/**
 * Find negative numbers from an array of numbers
 **/

predicate IsNegative(n: int)
{
    n < 0
}

// <vc-helpers>
lemma SeqAppendPreservesProperty(s: seq<int>, x: int)
    requires forall i :: 0 <= i < |s| ==> IsNegative(s[i])
    requires IsNegative(x)
    ensures forall i :: 0 <= i < |s + [x]| ==> IsNegative((s + [x])[i])
{
}

lemma SeqAppendPreservesInArray(s: seq<int>, x: int, arr: array<int>)
    requires forall i :: 0 <= i < |s| ==> s[i] in arr[..]
    requires x in arr[..]
    ensures forall i :: 0 <= i < |s + [x]| ==> (s + [x])[i] in arr[..]
{
}

lemma SeqAppendPreservesAllNegatives(s: seq<int>, x: int, arr: array<int>, j: int)
    requires 0 <= j < arr.Length
    requires forall i :: 0 <= i < j && IsNegative(arr[i]) ==> arr[i] in s
    requires IsNegative(arr[j])
    ensures forall i :: 0 <= i <= j && IsNegative(arr[i]) ==> arr[i] in (s + [arr[j]])
{
}
// </vc-helpers>

// <vc-spec>
method FindNegativeNumbers(arr: array<int>) returns (negativeList: seq<int>)
    // All numbers in the output are negative and exist in the input 
    ensures forall i :: 0 <= i < |negativeList| ==> IsNegative(negativeList[i]) && negativeList[i] in arr[..]
    // All negative numbers in the input are in the output
    ensures forall i :: 0 <= i < arr.Length && IsNegative(arr[i]) ==> arr[i] in negativeList
// </vc-spec>
// <vc-code>
{
    negativeList := [];
    var i := 0;
    
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant forall k :: 0 <= k < |negativeList| ==> IsNegative(negativeList[k]) && negativeList[k] in arr[..]
        invariant forall k :: 0 <= k < i && IsNegative(arr[k]) ==> arr[k] in negativeList
    {
        if IsNegative(arr[i]) {
            SeqAppendPreservesProperty(negativeList, arr[i]);
            SeqAppendPreservesInArray(negativeList, arr[i], arr);
            SeqAppendPreservesAllNegatives(negativeList, arr[i], arr, i);
            negativeList := negativeList + [arr[i]];
        }
        i := i + 1;
    }
}
// </vc-code>

