/**
 * Filter odd numbers from an array of numbers
 **/

predicate IsOdd(n: int)
{
    n % 2 != 0
}

// <vc-helpers>
lemma SeqAppendPreservesOddAndInArray(s: seq<int>, x: int, arr: array<int>)
    requires forall i :: 0 <= i < |s| ==> IsOdd(s[i]) && s[i] in arr[..]
    requires IsOdd(x) && x in arr[..]
    ensures forall i :: 0 <= i < |s + [x]| ==> IsOdd((s + [x])[i]) && (s + [x])[i] in arr[..]
{
}

lemma SeqAppendPreservesAllOddsIncluded(s: seq<int>, x: int, arr: array<int>, pos: nat)
    requires pos <= arr.Length
    requires forall i :: 0 <= i < pos && IsOdd(arr[i]) ==> arr[i] in s
    requires pos < arr.Length
    requires IsOdd(arr[pos])
    ensures forall i :: 0 <= i < pos && IsOdd(arr[i]) ==> arr[i] in (s + [arr[pos]])
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method FilterOddNumbers(arr: array<int>) returns (oddList: seq<int>)
    // All numbers in the output are odd and exist in the input 
    ensures forall i :: 0 <= i < |oddList| ==> IsOdd(oddList[i]) && oddList[i] in arr[..]
    // All odd numbers in the input are in the output
    ensures forall i :: 0 <= i < arr.Length && IsOdd(arr[i]) ==> arr[i] in oddList
// </vc-spec>
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
            SeqAppendPreservesOddAndInArray(oddList, arr[i], arr);
            SeqAppendPreservesAllOddsIncluded(oddList, arr[i], arr, i);
            oddList := oddList + [arr[i]];
        }
        i := i + 1;
    }
}
// </vc-code>
