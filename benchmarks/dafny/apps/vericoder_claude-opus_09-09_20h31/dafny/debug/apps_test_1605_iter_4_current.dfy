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
lemma SingleCharIsGood(s: string, i: int)
    requires ValidInput(s) && 0 <= i < |s|
    ensures IsGoodSubstring(s, i, i)
{
    var sub := s[i..i+1];
    assert |sub| == 1;
    assert MergeConsecutive(sub) == sub;
    assert IsPalindrome(sub);
}

lemma AllSingleCharsAreGood(s: string)
    requires ValidInput(s)
    ensures forall i :: 0 <= i < |s| ==> IsGoodSubstring(s, i, i)
{
    forall i | 0 <= i < |s|
        ensures IsGoodSubstring(s, i, i)
    {
        SingleCharIsGood(s, i);
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
    evenCount := 0;
    oddCount := 0;
    
    AllSingleCharsAreGood(s);
    
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant evenCount >= 0 && oddCount >= 0
    {
        var j := i;
        while j < |s|
            invariant i <= j <= |s|
            invariant evenCount >= 0 && oddCount >= 0
        {
            if IsGoodSubstring(s, i, j) {
                var len := j - i + 1;
                if len % 2 == 0 {
                    evenCount := evenCount + 1;
                } else {
                    oddCount := oddCount + 1;
                }
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    // Since all single character substrings are good (proven by AllSingleCharsAreGood)
    // and we've counted all substrings s[i..j], we have counted at least |s| odd substrings
    assert oddCount >= |s| by {
        // Each s[k..k] for 0 <= k < |s| is a good substring with odd length 1
        // We iterate through all i from 0 to |s|-1 and j from i to |s|-1
        // So we count each s[k..k] when i=k and j=k
    }
    
    // For the special case when |s| == 1
    if |s| == 1 {
        assert IsGoodSubstring(s, 0, 0);
        // We only have one possible substring s[0..0] which has odd length
        // So we should have evenCount == 0 and oddCount == 1
        assert evenCount == 0 && oddCount == 1;
    }
}
// </vc-code>

