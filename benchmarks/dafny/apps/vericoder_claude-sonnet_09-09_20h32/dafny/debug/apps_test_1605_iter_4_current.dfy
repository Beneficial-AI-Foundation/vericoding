predicate ValidInput(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b'
}

function MergeConsecutive(s: string): string
    requires |s| > 0
{
    if |s| == 1 then s
    else if s[0] == s[1] then MergeConsecutive(s[1..])
    else [s[0]] + MergeConsecutive(s[1..])
}

function IsPalindrome(s: string): bool
{
    if |s| <= 1 then true
    else s[0] == s[|s|-1] && IsPalindrome(s[1..|s|-1])
}

predicate IsGoodSubstring(s: string, i: int, j: int)
    requires ValidInput(s) && 0 <= i <= j < |s|
{
    var sub := s[i..j+1];
    IsPalindrome(MergeConsecutive(sub))
}

predicate ValidOutput(s: string, evenCount: int, oddCount: int)
    requires ValidInput(s)
{
    evenCount >= 0 && oddCount >= 0 &&
    evenCount + oddCount >= |s| &&
    oddCount >= |s| &&
    (|s| == 1 ==> evenCount == 0 && oddCount == 1)
}

// <vc-helpers>
lemma SingleCharIsPalindrome(c: char)
    ensures IsPalindrome([c])
{
}

lemma SingleCharGoodSubstring(s: string, i: int)
    requires ValidInput(s) && 0 <= i < |s|
    ensures IsGoodSubstring(s, i, i)
{
    var sub := s[i..i+1];
    assert sub == [s[i]];
    assert MergeConsecutive(sub) == [s[i]];
    SingleCharIsPalindrome(s[i]);
}

lemma AllSingleCharsAreGood(s: string)
    requires ValidInput(s)
    ensures forall i :: 0 <= i < |s| ==> IsGoodSubstring(s, i, i)
{
    forall i | 0 <= i < |s|
        ensures IsGoodSubstring(s, i, i)
    {
        SingleCharGoodSubstring(s, i);
    }
}

lemma SubstringCountLemma(n: int)
    requires n > 0
    ensures n * (n + 1) / 2 >= n
{
}

lemma OddCountLowerBound(n: int, i: int)
    requires n > 0 && 0 <= i <= n
    ensures (n - i) * (n - i + 1) / 2 - (n - i) / 2 >= n - i
{
    var remaining := n - i;
    if remaining == 0 {
        assert remaining * (remaining + 1) / 2 - remaining / 2 == 0;
        assert remaining == 0;
    } else {
        assert remaining > 0;
        assert remaining * (remaining + 1) / 2 >= remaining;
        assert remaining / 2 <= remaining;
        assert remaining * (remaining + 1) / 2 - remaining / 2 >= remaining - remaining;
        assert remaining * (remaining + 1) / 2 - remaining / 2 >= 0;
        if remaining == 1 {
            assert remaining * (remaining + 1) / 2 - remaining / 2 == 1 * 2 / 2 - 1 / 2 == 1 - 0 == 1;
        } else {
            assert remaining >= 2;
            assert remaining * (remaining + 1) / 2 >= remaining * remaining / 2;
            assert remaining * remaining / 2 >= remaining;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (evenCount: int, oddCount: int)
    requires ValidInput(s)
    ensures ValidOutput(s, evenCount, oddCount)
// </vc-spec>
// <vc-code>
{
    var n := |s|;
    evenCount := 0;
    oddCount := 0;
    
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant evenCount >= 0 && oddCount >= 0
        invariant oddCount >= n - i
    {
        var j := i;
        while j < n
            invariant i <= j <= n
            invariant evenCount >= 0 && oddCount >= 0
            invariant oddCount >= (n - i) - (j - i) + (j - i + 1) / 2
        {
            var len := j - i + 1;
            if len % 2 == 0 {
                evenCount := evenCount + 1;
            } else {
                oddCount := oddCount + 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    AllSingleCharsAreGood(s);
    SubstringCountLemma(n);
}
// </vc-code>

