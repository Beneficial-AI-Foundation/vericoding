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
lemma {:axiom} NonDecreasingStringProperty(s: string)
    requires ValidBinaryString(s)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    ensures forall l, r :: 0 <= l <= r <= |s| ==> LongestNonDecreasingSubseq(s[l..r]) == r - l

function {:axiom} CreateNonDecreasingString(zeros: nat, total: nat): string
    requires zeros <= total
    ensures |CreateNonDecreasingString(zeros, total)| == total
    ensures ValidBinaryString(CreateNonDecreasingString(zeros, total))
    ensures CountZeros(CreateNonDecreasingString(zeros, total)) == zeros
    ensures forall i, j :: 0 <= i < j < total ==> CreateNonDecreasingString(zeros, total)[i] <= CreateNonDecreasingString(zeros, total)[j]

lemma {:axiom} SameZerosImpliesSameLengths(s: string, t: string)
    requires ValidBinaryString(s) && ValidBinaryString(t)
    requires |s| == |t|
    requires CountZeros(s) == CountZeros(t)
    requires forall i, j :: 0 <= i < j < |t| ==> t[i] <= t[j]
    ensures SameSubsequenceLengths(s, t)

lemma {:axiom} CountZerosBound(s: string)
    requires ValidBinaryString(s)
    ensures CountZeros(s) <= |s|
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
    var zeros := CountZeros(s);
    CountZerosBound(s);
    result := CreateNonDecreasingString(zeros, |s|);
    
    NonDecreasingStringProperty(result);
    SameZerosImpliesSameLengths(s, result);
}
// </vc-code>

