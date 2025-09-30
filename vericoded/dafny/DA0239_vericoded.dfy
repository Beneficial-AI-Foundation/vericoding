predicate ValidInput(n: int) {
    n >= 1
}

function WorstCasePresses(n: int): int
    requires ValidInput(n)
{
    n * (n * n + 5) / 6
}

// <vc-helpers>
lemma WorstCasePressesPositive(n: int)
    requires ValidInput(n)
    ensures WorstCasePresses(n) >= 1
{
    assert n >= 1;
    assert n * n >= 1;
    assert n * n + 5 >= 6;
    assert n * (n * n + 5) >= 6;
    assert n * (n * n + 5) / 6 >= 1;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == WorstCasePresses(n)
    ensures result >= 1
// </vc-spec>
// <vc-code>
{
    var nsquared := n * n;
    result := n * (nsquared + 5) / 6;
    
    WorstCasePressesPositive(n);
}
// </vc-code>

