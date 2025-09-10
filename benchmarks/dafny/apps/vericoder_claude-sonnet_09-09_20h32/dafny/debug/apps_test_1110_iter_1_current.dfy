predicate ValidInput(n: int) {
    n >= 1
}

function WorstCasePresses(n: int): int
    requires ValidInput(n)
{
    n * (n * n + 5) / 6
}

// <vc-helpers>
lemma WorstCasePositive(n: int)
    requires ValidInput(n)
    ensures WorstCasePresses(n) >= 1
{
    assert n >= 1;
    assert n * n >= 1;
    assert n * n + 5 >= 6;
    assert n * (n * n + 5) >= n * 6;
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
    result := n * (n * n + 5) / 6;
    WorstCasePositive(n);
}
// </vc-code>

