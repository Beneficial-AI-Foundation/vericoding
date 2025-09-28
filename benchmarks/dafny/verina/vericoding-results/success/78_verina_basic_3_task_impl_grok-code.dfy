// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsDivisibleBy11(n: int) returns (result: bool)
    ensures result <==> (exists k: int :: k * 11 == n)
// </vc-spec>
// <vc-code>
{
    var k := n / 11;
    result := k * 11 == n;
}
// </vc-code>
