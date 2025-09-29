/**
 * Filter odd numbers from an array of numbers
 **/

predicate IsOdd(n: int)
{
    n % 2 != 0
}

// <vc-helpers>
lemma OddListProperties(arr: array<int>, oddList: seq<int>, k: int)
    requires 0 <= k <= arr.Length
    requires oddList == GetOddPrefix(arr, k)
    ensures forall i :: 0 <= i < |oddList| ==> IsOdd(oddList[i]) && oddList[i] in arr[..]
    ensures forall i :: 0 <= i < k && IsOdd(arr[i]) ==> arr[i] in oddList
    decreases k
{
    if k == 0 {
        assert oddList == [];
    } else {
        var prevList := GetOddPrefix(arr, k-1);
        OddListProperties(arr, prevList, k-1);
        
        if IsOdd(arr[k-1]) {
            assert oddList == prevList + [arr[k-1]];
            assert arr[k-1] in oddList;
        } else {
            assert oddList == prevList;
        }
    }
}

function GetOddPrefix(arr: array<int>, k: int): seq<int>
    requires 0 <= k <= arr.Length
    reads arr
    decreases k
{
    if k == 0 then []
    else 
        var prevOdds := GetOddPrefix(arr, k-1);
        if IsOdd(arr[k-1]) then prevOdds + [arr[k-1]] else prevOdds
}
// </vc-helpers>

// <vc-spec>
method FilterOddNumbers(arr: array<int>) returns (oddList: seq<int>)
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
        invariant oddList == GetOddPrefix(arr, i)
        invariant forall j :: 0 <= j < |oddList| ==> IsOdd(oddList[j]) && oddList[j] in arr[..]
        invariant forall j :: 0 <= j < i && IsOdd(arr[j]) ==> arr[j] in oddList
    {
        if IsOdd(arr[i]) {
            oddList := oddList + [arr[i]];
        }
        i := i + 1;
    }
    
    OddListProperties(arr, oddList, arr.Length);
}
// </vc-code>

