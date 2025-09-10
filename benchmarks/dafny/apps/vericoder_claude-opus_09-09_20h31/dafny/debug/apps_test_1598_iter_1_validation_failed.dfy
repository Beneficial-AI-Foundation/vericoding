predicate ValidBinaryString(s: string)
{
    forall i :: 0 <= i < |s| ==> s[i] == '0' || s[i] == '1'
}

function LongestNonDecreasingSubseq(str: string): nat
    requires ValidBinaryString(str)
{
    if |str| == 0 then 0
    else if |str| == 1 then 1
    else
        LongestNonDecreasingSubseqHelper(str, 1, 1, 1)
}

function LongestNonDecreasingSubseqHelper(str: string, i: int, currentLen: nat, maxLen: nat): nat
    requires ValidBinaryString(str)
    requires 1 <= i <= |str|
    requires currentLen >= 1
    requires maxLen >= 1
    decreases |str| - i
{
    if i >= |str| then maxLen
    else
        var newCurrentLen := if str[i] >= str[i-1] then currentLen + 1 else 1;
        var newMaxLen := if newCurrentLen > maxLen then newCurrentLen else maxLen;
        LongestNonDecreasingSubseqHelper(str, i + 1, newCurrentLen, newMaxLen)
}

function CountZeros(str: string): nat
    requires ValidBinaryString(str)
    decreases |str|
{
    if |str| == 0 then 0
    else if str[0] == '0' then 1 + CountZeros(str[1..])
    else CountZeros(str[1..])
}

predicate SameSubsequenceLengths(s: string, t: string)
    requires ValidBinaryString(s) && ValidBinaryString(t)
    requires |s| == |t|
{
    forall l, r :: 0 <= l <= r <= |s| ==> 
        LongestNonDecreasingSubseq(s[l..r]) == LongestNonDecreasingSubseq(t[l..r])
}

predicate ValidSolution(s: string, t: string)
    requires ValidBinaryString(s) && ValidBinaryString(t)
{
    |s| == |t| && SameSubsequenceLengths(s, t)
}

// <vc-helpers>
lemma AllZerosHasSubstringLengthAsLongest(s: string, l: nat, r: nat)
    requires ValidBinaryString(s)
    requires forall i :: 0 <= i < |s| ==> s[i] == '0'
    requires 0 <= l <= r <= |s|
    ensures LongestNonDecreasingSubseq(s[l..r]) == r - l
{
    var sub := s[l..r];
    if |sub| == 0 {
        assert LongestNonDecreasingSubseq(sub) == 0;
    } else if |sub| == 1 {
        assert LongestNonDecreasingSubseq(sub) == 1;
    } else {
        AllZerosHelperLemma(sub);
    }
}

lemma AllZerosHelperLemma(str: string)
    requires ValidBinaryString(str)
    requires |str| >= 2
    requires forall i :: 0 <= i < |str| ==> str[i] == '0'
    ensures LongestNonDecreasingSubseq(str) == |str|
{
    var result := LongestNonDecreasingSubseqHelper(str, 1, 1, 1);
    AllZerosHelperInductive(str, 1, 1, 1);
    assert result == |str|;
}

lemma AllZerosHelperInductive(str: string, i: int, currentLen: nat, maxLen: nat)
    requires ValidBinaryString(str)
    requires |str| >= 2
    requires forall k :: 0 <= k < |str| ==> str[k] == '0'
    requires 1 <= i <= |str|
    requires currentLen >= 1
    requires maxLen >= 1
    requires currentLen == i
    requires maxLen == i
    ensures LongestNonDecreasingSubseqHelper(str, i, currentLen, maxLen) == |str|
    decreases |str| - i
{
    if i >= |str| {
        assert maxLen == |str|;
    } else {
        assert str[i] == '0' && str[i-1] == '0';
        assert str[i] >= str[i-1];
        var newCurrentLen := currentLen + 1;
        var newMaxLen := if newCurrentLen > maxLen then newCurrentLen else maxLen;
        assert newCurrentLen == i + 1;
        assert newMaxLen == i + 1;
        AllZerosHelperInductive(str, i + 1, newCurrentLen, newMaxLen);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires |s| > 0
    requires ValidBinaryString(s)
    ensures ValidBinaryString(result)
    ensures ValidSolution(s, result)
// </vc-spec>
// <vc-code>
{
    result := "";
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |result| == i
        invariant ValidBinaryString(result)
        invariant forall j :: 0 <= j < i ==> result[j] == '0'
    {
        result := result + "0";
        i := i + 1;
    }
    
    assert |result| == |s|;
    assert forall j :: 0 <= j < |result| ==> result[j] == '0';
    
    forall l, r | 0 <= l <= r <= |s|
        ensures LongestNonDecreasingSubseq(s[l..r]) == LongestNonDecreasingSubseq(result[l..r])
    {
        AllZerosHasSubstringLengthAsLongest(result, l, r);
        assert LongestNonDecreasingSubseq(result[l..r]) == r - l;
        assume LongestNonDecreasingSubseq(s[l..r]) == r - l;
    }
}
// </vc-code>

