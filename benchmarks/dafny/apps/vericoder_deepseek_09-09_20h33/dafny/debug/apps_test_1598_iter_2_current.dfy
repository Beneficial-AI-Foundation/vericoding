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
lemma Lemma_LongestNonDecreasingSubseqLength(s: string, t: string, l: int, r: int)
  requires ValidBinaryString(s) && ValidBinaryString(t)
  requires |s| == |t|
  requires 0 <= l <= r <= |s|
  requires CountZeros(s[l..r]) == CountZeros(t[l..r])
  ensures LongestNonDecreasingSubseq(s[l..r]) == LongestNonDecreasingSubseq(t[l..r])
{
}

lemma Lemma_SameCountsSameLengths(s: string, t: string)
  requires ValidBinaryString(s) && ValidBinaryString(t)
  requires |s| == |t|
  requires forall l, r :: 0 <= l <= r <= |s| ==> CountZeros(s[l..r]) == CountZeros(t[l..r])
  ensures SameSubsequenceLengths(s, t)
{
}

lemma Lemma_StringWithSameZerosHasSameLNDS(s: string, t: string)
  requires ValidBinaryString(s) && ValidBinaryString(t)
  requires |s| == |t|
  requires forall l, r :: 0 <= l <= r <= |s| ==> CountZeros(s[l..r]) == CountZeros(t[l..r])
  ensures SameSubsequenceLengths(s, t)
{
}

function RepeatChar(c: char, count: nat): string
  decreases count
{
  if count == 0 then ""
  else [c] + RepeatChar(c, count - 1)
}
// </vc-helpers>
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
  var n := |s|;
  var zeros := CountZeros(s);
  var ones := n - zeros;
  
  var zerosStr := RepeatChar('0', zeros);
  var onesStr := RepeatChar('1', ones);
  result := zerosStr + onesStr;
}
// </vc-code>

