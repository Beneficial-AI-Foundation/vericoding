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
}

lemma countBounds(n: int)
    requires n >= 1
    ensures n * (n + 1) / 2 >= 0
    ensures n * (n + 1) / 2 >= n
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
    {
        var j := i + 1;
        while j <= n
            invariant i < j <= n + 1
            invariant result >= 0
        {
            if j <= n {
                var substring := s[i..j];
                if |substring| > 0 {
                    substringToIntBounds(s, i, j);
                    var val := substringToInt(substring);
                    if val % p == 0 {
                        result := result + 1;
                    }
                }
            }
            j := j + 1;
        }
        i := i + 1;
    }
}
// </vc-code>

