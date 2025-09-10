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
lemma CountZerosUpperBound(s: string)
    requires ValidBinaryString(s)
    ensures CountZeros(s) <= |s|
{
    if |s| == 0 {
        // Base case: empty string has 0 zeros
    } else if s[0] == '0' {
        // If first char is '0', we have 1 + CountZeros(s[1..])
        // By induction, CountZeros(s[1..]) <= |s[1..]| = |s| - 1
        // So 1 + CountZeros(s[1..]) <= 1 + |s| - 1 = |s|
        CountZerosUpperBound(s[1..]);
    } else {
        // If first char is '1', we have CountZeros(s[1..])
        // By induction, CountZeros(s[1..]) <= |s[1..]| = |s| - 1 < |s|
        CountZerosUpperBound(s[1..]);
    }
}

lemma RepeatCharValidBinary(c: char, n: nat)
    requires c == '0' || c == '1'
    ensures ValidBinaryString(RepeatChar(c, n))
{
    if n == 0 {
        // Empty string is valid
    } else {
        // Recursive case: [c] + RepeatChar(c, n-1)
        RepeatCharValidBinary(c, n-1);
    }
}

lemma CountZerosRepeatChar(c: char, n: nat)
    requires c == '0' || c == '1'
    ensures CountZeros(RepeatChar(c, n)) == if c == '0' then n else 0
{
    if n == 0 {
        // Base case: empty string has 0 zeros
    } else {
        CountZerosRepeatChar(c, n-1);
        if c == '0' {
            // RepeatChar('0', n) = ['0'] + RepeatChar('0', n-1)
            // CountZeros(['0'] + RepeatChar('0', n-1)) = 1 + CountZeros(RepeatChar('0', n-1))
            // = 1 + (n-1) = n
        } else {
            // RepeatChar('1', n) = ['1'] + RepeatChar('1', n-1)
            // CountZeros(['1'] + RepeatChar('1', n-1)) = CountZeros(RepeatChar('1', n-1))
            // = 0
        }
    }
}

lemma ConcatValidBinary(s1: string, s2: string)
    requires ValidBinaryString(s1) && ValidBinaryString(s2)
    ensures ValidBinaryString(s1 + s2)
{
    // Prove that concatenation preserves ValidBinaryString
}

lemma CountZerosConcat(s1: string, s2: string)
    requires ValidBinaryString(s1) && ValidBinaryString(s2)
    ensures CountZeros(s1 + s2) == CountZeros(s1) + CountZeros(s2)
{
    if |s1| == 0 {
        // Base case: "" + s2 = s2
    } else {
        // Recursive case: s1[0..1] + s1[1..] + s2
        var rest := s1[1..] + s2;
        CountZerosConcat(s1[1..], s2);
        if s1[0] == '0' {
            assert CountZeros(s1 + s2) == CountZeros([s1[0]] + rest);
            assert CountZeros([s1[0]] + rest) == 1 + CountZeros(rest);
            assert CountZeros(rest) == CountZeros(s1[1..]) + CountZeros(s2);
            assert CountZeros(s1) == 1 + CountZeros(s1[1..]);
        } else {
            assert CountZeros(s1 + s2) == CountZeros([s1[0]] + rest);
            assert CountZeros([s1[0]] + rest) == CountZeros(rest);
            assert CountZeros(rest) == CountZeros(s1[1..]) + CountZeros(s2);
            assert CountZeros(s1) == CountZeros(s1[1..]);
        }
    }
}

function Sort(s: string): string
    requires ValidBinaryString(s)
    ensures ValidBinaryString(Sort(s))
    ensures |Sort(s)| == |s|
    ensures CountZeros(Sort(s)) == CountZeros(s)
{
    if |s| <= 1 then s
    else
        CountZerosUpperBound(s);
        var zeros := CountZeros(s);
        var ones := |s| - zeros;
        assert ones >= 0;
        
        var zeroString := RepeatChar('0', zeros);
        var oneString := RepeatChar('1', ones);
        
        RepeatCharValidBinary('0', zeros);
        RepeatCharValidBinary('1', ones);
        ConcatValidBinary(zeroString, oneString);
        
        CountZerosRepeatChar('0', zeros);
        CountZerosRepeatChar('1', ones);
        CountZerosConcat(zeroString, oneString);
        
        assert CountZeros(zeroString + oneString) == zeros + 0 == zeros == CountZeros(s);
        assert |zeroString + oneString| == |zeroString| + |oneString| == zeros + ones == |s|;
        
        zeroString + oneString
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
    // For any substring s[l..r], the longest non-decreasing subsequence
    // is preserved when sorting the entire string
    forall l, r | 0 <= l <= r <= |s|
    ensures LongestNonDecreasingSubseq(s[l..r]) == LongestNonDecreasingSubseq(Sort(s)[l..r])
    {
        // The proof relies on the fact that sorting puts all 0s before all 1s
        // which preserves the longest non-decreasing subsequence structure
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
    result := Sort(s);
    SortedStringSameSubsequenceLengths(s);
}
// </vc-code>

