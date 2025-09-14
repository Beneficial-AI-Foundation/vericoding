// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): function to compute quotient when divisible by 11 */
function GetQuotientIfDivisible(n: int): int
    requires n % 11 == 0
    ensures GetQuotientIfDivisible(n) * 11 == n
{
    n / 11
}
// </vc-helpers>

// <vc-spec>
method IsDivisibleBy11(n: int) returns (result: bool)
    ensures result <==> (exists k: int :: k * 11 == n)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): implementation using helper function */
{
    if n % 11 == 0 {
        var k := GetQuotientIfDivisible(n);
        assert k * 11 == n;
        result := true;
    } else {
        result := false;
    }
}
// </vc-code>
