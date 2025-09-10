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
        invariant oddCount >= i  // Each position contributes at least one odd substring (itself)
    {
        var j := i;
        var countedSingleChar := false;
        while j < |s|
            invariant i <= j <= |s|
            invariant evenCount >= 0 && oddCount >= 0
            invariant countedSingleChar ==> oddCount >= i + 1  // If we've processed s[i..i], oddCount increased
        {
            if IsGoodSubstring(s, i, j) {
                var len := j - i + 1;
                if len % 2 == 0 {
                    evenCount := evenCount + 1;
                } else {
                    oddCount := oddCount + 1;
                    if j == i {
                        countedSingleChar := true;
                    }
                }
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    // Verify that we've counted at least all single character substrings
    assert oddCount >= |s|;
    
    // For the special case when |s| == 1
    if |s| == 1 {
        assert IsGoodSubstring(s, 0, 0);
        // We know we counted s[0..0] which has odd length
        // So oddCount >= 1
        // Since we only have one possible substring, set the counts exactly
        evenCount := 0;
        oddCount := 1;
    }
}
// </vc-code>

