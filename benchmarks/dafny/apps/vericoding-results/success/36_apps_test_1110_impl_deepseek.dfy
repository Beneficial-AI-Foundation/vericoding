predicate ValidInput(n: int) {
    n >= 1
}

function WorstCasePresses(n: int): int
    requires ValidInput(n)
{
    n * (n * n + 5) / 6
}

// <vc-helpers>
lemma WorstCasePressesFormula(n: int)
    requires ValidInput(n)
    ensures WorstCasePresses(n) == n * (n * n + 5) / 6
{
}

lemma WorstCasePressesPositive(n: int)
    requires ValidInput(n)
    ensures WorstCasePresses(n) >= 1
{
    var n2 := n * n;
    var numerator := n * (n2 + 5);
    // Since n >= 1, n2 + 5 >= 6, so numerator >= 6
    // Division by 6 gives at least 1
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
}
// </vc-code>

