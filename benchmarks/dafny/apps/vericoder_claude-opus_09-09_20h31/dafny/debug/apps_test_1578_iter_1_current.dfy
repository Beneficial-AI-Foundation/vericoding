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
        // n is even, so n * (n-1) = even * odd = even
        assert n * (n - 1) == n * (n - 1);
    } else {
        // n is odd, so (n-1) is even, thus n * (n-1) = odd * even = even
        assert (n - 1) % 2 == 0;
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

