predicate ValidInput(n: int) {
    n >= 1
}

function MaxDistributions(n: int): int
    requires ValidInput(n)
{
    if n % 3 == 0 then 2 * (n / 3) else 2 * (n / 3) + 1
}

// <vc-helpers>
lemma MaxDistributionsPositive(n: int)
    requires ValidInput(n)
    ensures MaxDistributions(n) >= 1
{
    if n % 3 == 0 {
        assert n >= 3;
        assert n / 3 >= 1;
        assert 2 * (n / 3) >= 2;
    } else {
        assert n / 3 >= 0;
        assert 2 * (n / 3) + 1 >= 1;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result >= 1
    ensures result == MaxDistributions(n)
// </vc-spec>
// <vc-code>
{
    MaxDistributionsPositive(n);
    if n % 3 == 0 {
        result := 2 * (n / 3);
    } else {
        result := 2 * (n / 3) + 1;
    }
}
// </vc-code>

