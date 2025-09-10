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
lemma substringToIntBounds(s: string, i: int, j: int)
    requires forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
    requires 0 <= i <= j <= |s|
    requires i < j
    ensures substringToInt(s[i..j]) >= 0
{
    var sub := s[i..j];
    assert forall k :: 0 <= k < |sub| ==> '0' <= sub[k] <= '9';
    substringToIntNonNegative(sub);
}

lemma substringToIntNonNegative(s: string)
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires |s| > 0
    ensures substringToInt(s) >= 0
{
    if |s| == 1 {
        assert s[0] as int - '0' as int >= 0;
    } else {
        substringToIntNonNegative(s[..|s|-1]);
        assert substringToInt(s[..|s|-1]) >= 0;
        assert s[|s|-1] as int - '0' as int >= 0;
        assert substringToInt(s) >= 0;
    }
}

lemma countBounds(n: int)
    requires n >= 1
    ensures n * (n + 1) / 2 >= 0
    ensures n * (n + 1) / 2 >= n
{
}

lemma triangularSum(n: int)
    requires n >= 0
    ensures (n * (n + 1)) / 2 == if n == 0 then 0 else (n * (n + 1)) / 2
{
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
        invariant result >= 0
        invariant result <= i * n - i * (i - 1) / 2
    {
        var j := i + 1;
        var localCount := 0;
        while j <= n
            invariant i < j <= n + 1
            invariant result >= 0
            invariant localCount >= 0
            invariant localCount <= j - i - 1
        {
            if j <= n {
                var substring := s[i..j];
                if |substring| > 0 {
                    substringToIntBounds(s, i, j);
                    var val := substringToInt(substring);
                    if val % p == 0 {
                        localCount := localCount + 1;
                    }
                }
            }
            j := j + 1;
        }
        result := result + localCount;
        i := i + 1;
    }
    assert result <= n * (n + 1) / 2;
}
// </vc-code>

