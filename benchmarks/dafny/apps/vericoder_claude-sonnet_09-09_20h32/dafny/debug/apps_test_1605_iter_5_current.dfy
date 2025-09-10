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

lemma OddCountInvariant(i: int, j: int, n: int, oddCount: int)
    requires 0 <= i <= j <= n
    requires oddCount >= 0
    ensures oddCount >= 0
{
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
        invariant oddCount >= 0
    {
        var j := i;
        while j < n
            invariant i <= j <= n
            invariant evenCount >= 0 && oddCount >= 0
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

