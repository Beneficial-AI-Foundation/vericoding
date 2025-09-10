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
function countGoodSubstrings(s: string): (evenCount: int, oddCount: int)
    requires ValidInput(s)
    ensures evenCount >= 0 && oddCount >= 0 && evenCount + oddCount == |s| * (|s| + 1) / 2
{
    var evenC := 0;
    var oddC := 0;
    for i := 0 to |s| - 1
        invariant 0 <= i <= |s|
        invariant evenC >= 0 && oddC >= 0
        invariant evenC + oddC == i * (i + 1) / 2
    {
        for j := i to |s| - 1
            invariant i <= j <= |s|
            invariant evenC >= 0 && oddC >= 0
            invariant evenC + oddC == i * (i + 1) / 2 + (j - i) // Sum of lengths up to j-1 starts from i
        {
            var sub := s[i..j+1];
            if IsPalindrome(MergeConsecutive(sub)) {
                if (|sub| % 2 == 0) {
                    evenC := evenC + 1;
                } else {
                    oddC := oddC + 1;
                }
            }
        }
    }
    return evenC, oddC;
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (evenCount: int, oddCount: int)
    requires ValidInput(s)
    ensures ValidOutput(s, evenCount, oddCount)
// </vc-spec>
// <vc-code>
{
    var evenC := 0;
    var oddC := 0;

    for i := 0 to |s| - 1
        invariant 0 <= i <= |s|
        invariant evenC >= 0 && oddC >= 0
    {
        for j := i to |s| - 1
            invariant i <= j < |s|
            invariant evenC >= 0 && oddC >= 0
        {
            var sub := s[i..j+1];
            if IsPalindrome(MergeConsecutive(sub)) {
                if ((j - i + 1) % 2 == 0) {
                    evenC := evenC + 1;
                } else {
                    oddC := oddC + 1;
                }
            }
        }
    }
    evenCount := evenC;
    oddCount := oddC;
}
// </vc-code>

