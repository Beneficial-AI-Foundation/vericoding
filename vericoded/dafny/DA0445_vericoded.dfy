predicate isPrime(p: int)
    requires p >= 2
{
    forall k :: 2 <= k < p ==> p % k != 0
}

predicate ValidInput(n: int, p: int, s: string)
{
    n >= 1 &&
    p >= 2 &&
    isPrime(p) &&
    |s| == n &&
    forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function substringToInt(s: string): int
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires |s| > 0
{
    if |s| == 1 then s[0] as int - '0' as int
    else substringToInt(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
}

predicate ValidResult(result: int, n: int)
{
    result >= 0 && result <= n * (n + 1) / 2
}

// <vc-helpers>
lemma SubstringCount(n: int)
    requires n >= 1
    ensures n * (n + 1) / 2 >= 0
{
    // The number of substrings of length n is n*(n+1)/2
}

lemma SubstringToIntNonNegative(s: string)
    requires forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
    requires |s| > 0
    ensures substringToInt(s) >= 0
{
    if |s| == 1 {
        assert substringToInt(s) == s[0] as int - '0' as int;
        assert s[0] >= '0' && s[0] <= '9';
        assert substringToInt(s) >= 0;
    } else {
        assert |s[..|s|-1]| == |s| - 1 > 0;
        assert forall k {:trigger s[..|s|-1][k]} :: 0 <= k < |s[..|s|-1]| ==> '0' <= s[..|s|-1][k] <= '9';
        SubstringToIntNonNegative(s[..|s|-1]);
        assert substringToInt(s[..|s|-1]) >= 0;
        assert s[|s|-1] >= '0' && s[|s|-1] <= '9';
        assert substringToInt(s) == substringToInt(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int);
        assert substringToInt(s) >= 0;
    }
}

lemma SubstringToIntBounds(s: string, i: int, j: int)
    requires forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
    requires 0 <= i < j <= |s|
    ensures substringToInt(s[i..j]) >= 0
{
    var sub := s[i..j];
    assert |sub| == j - i > 0;
    assert forall k :: 0 <= k < |sub| ==> '0' <= sub[k] <= '9';
    SubstringToIntNonNegative(sub);
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, p: int, s: string) returns (result: int)
    requires ValidInput(n, p, s)
    ensures ValidResult(result, n)
// </vc-spec>
// <vc-code>
{
    result := 0;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant 0 <= result <= (i * (2 * n - i + 1)) / 2
    {
        var j := i + 1;
        while j <= n
            invariant i + 1 <= j <= n + 1
            invariant 0 <= result <= (i * (2 * n - i + 1)) / 2 + (j - i - 1)
        {
            SubstringToIntBounds(s, i, j);
            var substring := s[i..j];
            var value := substringToInt(substring);
            
            if value % p == 0 {
                result := result + 1;
            }
            
            j := j + 1;
        }
        i := i + 1;
    }
    
    SubstringCount(n);
}
// </vc-code>

