// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added assertion to prove evenness via associativity */
lemma ProductIsEven(n: int)
    ensures (n * (n + 1)) % 2 == 0
{
    if n % 2 == 0 {
        var k := n / 2;
        assert n == 2 * k;
        assert n * (n + 1) == 2 * k * (n + 1);
        assert (2 * (k * (n + 1))) % 2 == 0;
    } else {
        assert (n + 1) % 2 == 0;
        var k := (n + 1) / 2;
        assert n + 1 == 2 * k;
        assert n * (n + 1) == n * (2 * k);
        assert n * (2 * k) == (n * k) * 2;
        assert (n * (2 * k)) % 2 == 0;
    }
}
// </vc-helpers>

// <vc-spec>
method CountNonEmptySubstrings(s: string) returns (count: int)
    ensures count >= 0
    ensures count == (|s| * (|s| + 1)) / 2
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): switched to a direct calculation using the closed-form formula */
{
    var n := |s|;
    ProductIsEven(n);
    count := (n * (n + 1)) / 2;
}
// </vc-code>
