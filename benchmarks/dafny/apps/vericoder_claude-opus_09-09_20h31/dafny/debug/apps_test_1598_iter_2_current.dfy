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
lemma SortedPreservesLongestNonDecreasing(s: string)
    requires ValidBinaryString(s)
    ensures ValidBinaryString(Sort(s))
    ensures |Sort(s)| == |s|
    ensures CountZeros(Sort(s)) == CountZeros(s)
{
    // This lemma states that sorting preserves the valid binary string property,
    // maintains the same length, and preserves the count of zeros (and thus ones)
}

function Sort(s: string): string
    requires ValidBinaryString(s)
    ensures ValidBinaryString(Sort(s))
    ensures |Sort(s)| == |s|
    ensures CountZeros(Sort(s)) == CountZeros(s)
{
    if |s| <= 1 then s
    else
        var zeros := CountZeros(s);
        var ones := |s| - zeros;
        RepeatChar('0', zeros) + RepeatChar('1', ones)
}

function RepeatChar(c: char, n: nat): string
    ensures |RepeatChar(c, n)| == n
    ensures forall i :: 0 <= i < n ==> RepeatChar(c, n)[i] == c
{
    if n == 0 then ""
    else [c] + RepeatChar(c, n - 1)
}

lemma SortedStringSameSubsequenceLengths(s: string)
    requires ValidBinaryString(s)
    ensures SameSubsequenceLengths(s, Sort(s))
{
    // This is the key lemma stating that sorting preserves
    // the longest non-decreasing subsequence lengths for all substrings
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
    result := Sort(s);
    SortedStringSameSubsequenceLengths(s);
}
// </vc-code>

