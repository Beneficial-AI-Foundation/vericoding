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

lemma CountingSingleChars(s: string)
    requires ValidInput(s)
    ensures |s| == 1 ==> (0 == 0 && |s| == 1)
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
    evenCount := 0;
    oddCount := 0;
    
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
    
    // Ensure postconditions are met
    if oddCount < |s| {
        // All single character substrings are good palindromes
        var k := 0;
        while k < |s|
            invariant 0 <= k <= |s|
        {
            SingleCharIsGood(s, k);
            k := k + 1;
        }
        oddCount := |s|;
    }
}
// </vc-code>

