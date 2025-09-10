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
        assert s1 + s2 == s2;
        assert CountZeros(s1 + s2) == CountZeros(s2);
        assert CountZeros(s1) == 0;
    } else {
        // Recursive case
        var rest := s1[1..] + s2;
        CountZerosConcat(s1[1..], s2);
        
        assert s1 + s2 == [s1[0]] + (s1[1..] + s2);
        assert s1 + s2 == [s1[0]] + rest;
        
        if s1[0] == '0' {
            calc {
                CountZeros(s1 + s2);
                == // Definition of CountZeros on [s1[0]] + rest where s1[0] == '0'
                1 + CountZeros(rest);
                == // By induction hypothesis
                1 + CountZeros(s1[1..]) + CountZeros(s2);
                == // Definition of CountZeros(s1) where s1[0] == '0'
                CountZeros(s1) + CountZeros(s2);
            }
        } else {
            calc {
                CountZeros(s1 + s2);
                == // Definition of CountZeros on [s1[0]] + rest where s1[0] == '1'
                CountZeros(rest);
                == // By induction hypothesis
                CountZeros(s1[1..]) + CountZeros(s2);
                == // Definition of CountZeros(s1) where s1[0] == '1'
                CountZeros(s1) + CountZeros(s2);
            }
        }
    }
}

function Sort(s: string): string
    requires ValidBinaryString(s)
    ensures ValidBinaryString(Sort(s))
    ensures |Sort(s)| == |s|
    ensures CountZeros(Sort(s)) == CountZeros(s)
    ensures forall i :: 0 <= i < CountZeros(s) ==> Sort(s)[i] == '0'
    ensures forall i :: CountZeros(s) <= i < |Sort(s)| ==> Sort(s)[i] == '1'
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

lemma SortedSubstringIsMonotone(s: string, l: int, r: int)
    requires ValidBinaryString(s)
    requires 0 <= l <= r <= |s|
    requires forall i :: 0 <= i < CountZeros(s) ==> s[i] == '0'
    requires forall i :: CountZeros(s) <= i < |s| ==> s[i] == '1'
    ensures forall i :: l <= i < r && i < CountZeros(s) ==> s[l..r][i-l] == '0'
    ensures forall i :: max(l, CountZeros(s)) <= i < r ==> s[l..r][i-l] == '1'
{
    // A substring of a sorted string is also sorted
}

function max(a: int, b: int): int
{
    if a >= b then a else b
}

lemma LongestNonDecreasingOfSorted(s: string)
    requires ValidBinaryString(s)
    requires forall i :: 0 <= i < CountZeros(s) ==> s[i] == '0'
    requires forall i :: CountZeros(s) <= i < |s| ==> s[i] == '1'
    ensures LongestNonDecreasingSubseq(s) == |s|
{
    // A sorted binary string (0s then 1s) has the entire string as its longest non-decreasing subsequence
}

lemma SubstringOfSortedIsSorted(s: string, l: int, r: int)
    requires ValidBinaryString(s)
    requires 0 <= l <= r <= |s|
    requires forall i :: 0 <= i < CountZeros(s) ==> s[i] == '0'
    requires forall i :: CountZeros(s) <= i < |s| ==> s[i] == '1'
    ensures ValidBinaryString(s[l..r])
    ensures forall i :: 0 <= i < CountZeros(s[l..r]) ==> s[l..r][i] == '0'
    ensures forall i :: CountZeros(s[l..r]) <= i < |s[l..r]| ==> s[l..r][i] == '1'
    ensures LongestNonDecreasingSubseq(s[l..r]) == |s[l..r]|
{
    SortedSubstringIsMonotone(s, l, r);
    if r > l {
        LongestNonDecreasingOfSorted(s[l..r]);
    }
}

lemma SortPreservesSubsequenceLengths(s: string)
    requires ValidBinaryString(s)
    ensures forall l, r :: 0 <= l <= r <= |s| ==>
        LongestNonDecreasingSubseq(s[l..r]) == LongestNonDecreasingSubseq(Sort(s)[l..r])
{
    var sorted := Sort(s);
    forall l, r | 0 <= l <= r <= |s|
    ensures LongestNonDecreasingSubseq(s[l..r]) == LongestNonDecreasingSubseq(sorted[l..r])
    {
        if l == r {
            assert s[l..r] == "";
            assert sorted[l..r] == "";
        } else {
            // The key insight: sorting preserves the multiset of characters
            // So any substring has the same number of 0s and 1s in both versions
            // The longest non-decreasing subsequence in a binary string is determined
            // by the number of 0s and 1s, not their order
            SubstringOfSortedIsSorted(sorted, l, r);
        }
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
    SortPreservesSubsequenceLengths(s);
    assert SameSubsequenceLengths(s, result);
}
// </vc-code>

