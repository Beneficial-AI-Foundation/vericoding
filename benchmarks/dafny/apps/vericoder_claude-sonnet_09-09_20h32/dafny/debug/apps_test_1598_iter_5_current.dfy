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
lemma NonDecreasingStringProperty(s: string)
    requires ValidBinaryString(s)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    ensures forall l, r :: 0 <= l <= r <= |s| ==> LongestNonDecreasingSubseq(s[l..r]) == r - l
{
    forall l, r | 0 <= l <= r <= |s|
        ensures LongestNonDecreasingSubseq(s[l..r]) == r - l
    {
        var sub := s[l..r];
        if r - l <= 1 {
            if r - l == 0 {
                assert LongestNonDecreasingSubseq(sub) == 0;
            } else {
                assert LongestNonDecreasingSubseq(sub) == 1;
            }
        } else {
            assert forall i, j :: 0 <= i < j < |sub| ==> sub[i] <= sub[j];
            NonDecreasingStringLengthLemma(sub);
        }
    }
}

lemma NonDecreasingStringLengthLemma(s: string)
    requires ValidBinaryString(s)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    ensures LongestNonDecreasingSubseq(s) == |s|
{
    if |s| <= 1 {
        return;
    }
    NonDecreasingStringLengthHelperLemma(s, 1, 1, 1);
}

lemma NonDecreasingStringLengthHelperLemma(s: string, i: int, currentLen: nat, maxLen: nat)
    requires ValidBinaryString(s)
    requires forall x, y :: 0 <= x < y < |s| ==> s[x] <= s[y]
    requires 1 <= i <= |s|
    requires currentLen >= 1
    requires maxLen >= 1
    requires currentLen == i
    requires maxLen == i
    ensures LongestNonDecreasingSubseqHelper(s, i, currentLen, maxLen) == |s|
    decreases |s| - i
{
    if i >= |s| {
        return;
    }
    var newCurrentLen := if s[i] >= s[i-1] then currentLen + 1 else 1;
    var newMaxLen := if newCurrentLen > maxLen then newCurrentLen else maxLen;
    assert s[i] >= s[i-1];
    assert newCurrentLen == currentLen + 1 == i + 1;
    assert newMaxLen == i + 1;
    NonDecreasingStringLengthHelperLemma(s, i + 1, newCurrentLen, newMaxLen);
}

function CreateNonDecreasingString(zeros: nat, total: nat): string
    requires zeros <= total
    ensures |CreateNonDecreasingString(zeros, total)| == total
    ensures ValidBinaryString(CreateNonDecreasingString(zeros, total))
    ensures CountZeros(CreateNonDecreasingString(zeros, total)) == zeros
    ensures forall i, j :: 0 <= i < j < total ==> CreateNonDecreasingString(zeros, total)[i] <= CreateNonDecreasingString(zeros, total)[j]
{
    CreateNonDecreasingStringHelper(zeros, total - zeros)
}

function CreateNonDecreasingStringHelper(zeros: nat, ones: nat): string
    ensures |CreateNonDecreasingStringHelper(zeros, ones)| == zeros + ones
    ensures ValidBinaryString(CreateNonDecreasingStringHelper(zeros, ones))
    ensures CountZeros(CreateNonDecreasingStringHelper(zeros, ones)) == zeros
    ensures forall i, j :: 0 <= i < j < zeros + ones ==> CreateNonDecreasingStringHelper(zeros, ones)[i] <= CreateNonDecreasingStringHelper(zeros, ones)[j]
{
    if zeros == 0 then
        CreateOnesString(ones)
    else
        "0" + CreateNonDecreasingStringHelper(zeros - 1, ones)
}

function CreateOnesString(ones: nat): string
    ensures |CreateOnesString(ones)| == ones
    ensures ValidBinaryString(CreateOnesString(ones))
    ensures CountZeros(CreateOnesString(ones)) == 0
    ensures forall i :: 0 <= i < ones ==> CreateOnesString(ones)[i] == '1'
{
    if ones == 0 then ""
    else "1" + CreateOnesString(ones - 1)
}

lemma SameZerosImpliesSameLengths(s: string, t: string)
    requires ValidBinaryString(s) && ValidBinaryString(t)
    requires |s| == |t|
    requires CountZeros(s) == CountZeros(t)
    requires forall i, j :: 0 <= i < j < |t| ==> t[i] <= t[j]
    ensures SameSubsequenceLengths(s, t)
{
    forall l, r | 0 <= l <= r <= |s|
        ensures LongestNonDecreasingSubseq(s[l..r]) == LongestNonDecreasingSubseq(t[l..r])
    {
        var sSub := s[l..r];
        var tSub := t[l..r];
        
        assert ValidBinaryString(tSub);
        assert forall i, j :: 0 <= i < j < |tSub| ==> tSub[i] <= tSub[j];
        NonDecreasingStringProperty(t);
        assert LongestNonDecreasingSubseq(tSub) == r - l;
        
        CountZerosSubstring(s, l, r);
        CountZerosSubstring(t, l, r);
        
        SameLengthSameZerosImpliesSameNonDecreasingLength(sSub, tSub);
    }
}

lemma CountZerosSubstring(s: string, l: int, r: int)
    requires ValidBinaryString(s)
    requires 0 <= l <= r <= |s|
    ensures ValidBinaryString(s[l..r])
    ensures CountZeros(s[l..r]) <= r - l
{
    if l == r {
        assert s[l..r] == "";
        assert CountZeros(s[l..r]) == 0;
        assert r - l == 0;
        return;
    }
    CountZerosBound(s[l..r]);
}

lemma SameLengthSameZerosImpliesSameNonDecreasingLength(s: string, t: string)
    requires ValidBinaryString(s) && ValidBinaryString(t)
    requires |s| == |t|
    requires forall i, j :: 0 <= i < j < |t| ==> t[i] <= t[j]
    ensures LongestNonDecreasingSubseq(s) == LongestNonDecreasingSubseq(t)
{
    NonDecreasingStringLengthLemma(t);
    assert LongestNonDecreasingSubseq(t) == |t|;
    LongestNonDecreasingSubseqBound(s);
    assert LongestNonDecreasingSubseq(s) <= |s|;
    assert LongestNonDecreasingSubseq(s) == |s|;
}

lemma LongestNonDecreasingSubseqBound(s: string)
    requires ValidBinaryString(s)
    ensures LongestNonDecreasingSubseq(s) <= |s|
{
    if |s| <= 1 {
        return;
    }
    LongestNonDecreasingSubseqHelperBound(s, 1, 1, 1);
}

lemma LongestNonDecreasingSubseqHelperBound(s: string, i: int, currentLen: nat, maxLen: nat)
    requires ValidBinaryString(s)
    requires 1 <= i <= |s|
    requires currentLen >= 1
    requires maxLen >= 1
    requires currentLen <= i
    requires maxLen <= i
    ensures LongestNonDecreasingSubseqHelper(s, i, currentLen, maxLen) <= |s|
    decreases |s| - i
{
    if i >= |s| {
        return;
    }
    var newCurrentLen := if s[i] >= s[i-1] then currentLen + 1 else 1;
    var newMaxLen := if newCurrentLen > maxLen then newCurrentLen else maxLen;
    assert newCurrentLen <= i + 1;
    assert newMaxLen <= i + 1;
    LongestNonDecreasingSubseqHelperBound(s, i + 1, newCurrentLen, newMaxLen);
}

lemma CountZerosBound(s: string)
    requires ValidBinaryString(s)
    ensures CountZeros(s) <= |s|
{
    if |s| == 0 {
        return;
    }
    CountZerosBound(s[1..]);
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
    var zeros := CountZeros(s);
    CountZerosBound(s);
    result := CreateNonDecreasingString(zeros, |s|);
    
    NonDecreasingStringProperty(result);
    SameZerosImpliesSameLengths(s, result);
}
// </vc-code>

