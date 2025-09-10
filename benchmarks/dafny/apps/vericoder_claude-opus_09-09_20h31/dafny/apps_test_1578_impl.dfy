predicate ValidInput(n: int) {
    n >= 1
}

function MaxSum(n: int): int
    requires n >= 1
{
    n * (n - 1) / 2
}

// <vc-helpers>
lemma DivisionLemma(n: int)
    requires n >= 1
    ensures (n * (n - 1)) % 2 == 0
{
    if n % 2 == 0 {
        // n is even, so n = 2k for some k
        // n * (n-1) = 2k * (n-1) = 2 * (k * (n-1))
        // Therefore n * (n-1) is divisible by 2
        var k := n / 2;
        assert n == 2 * k;
        assert n * (n - 1) == (2 * k) * (n - 1);
        assert n * (n - 1) == 2 * (k * (n - 1));
        assert (n * (n - 1)) % 2 == 0;
    } else {
        // n is odd, so n-1 is even
        // n-1 = 2m for some m
        // n * (n-1) = n * 2m = 2 * (n * m)
        // Therefore n * (n-1) is divisible by 2
        assert n % 2 == 1;
        assert (n - 1) % 2 == 0;
        var m := (n - 1) / 2;
        assert n - 1 == 2 * m;
        assert n * (n - 1) == n * (2 * m);
        assert n * (n - 1) == 2 * (n * m);
        assert (n * (n - 1)) % 2 == 0;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == MaxSum(n)
// </vc-spec>
// <vc-code>
{
    DivisionLemma(n);
    result := n * (n - 1) / 2;
}
// </vc-code>

