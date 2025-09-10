function calculateDeposit(initial: int, years: int): int
    requires initial >= 0
    requires years >= 0
{
    if years == 0 then initial
    else 
        var prevDeposit := calculateDeposit(initial, years - 1);
        prevDeposit + prevDeposit / 100
}

// <vc-helpers>
lemma calculateDepositIncreases(initial: int, years: int)
    requires initial > 0
    requires years >= 0
    ensures calculateDeposit(initial, years + 1) > calculateDeposit(initial, years)
{
    var current := calculateDeposit(initial, years);
    var next := calculateDeposit(initial, years + 1);
    assert next == current + current / 100;
    assert current > 0;
    assert current / 100 >= 0;
    assert next > current;
}

lemma calculateDepositMonotonic(initial: int, y1: int, y2: int)
    requires initial > 0
    requires 0 <= y1 <= y2
    ensures calculateDeposit(initial, y1) <= calculateDeposit(initial, y2)
{
    if y1 == y2 {
    } else {
        calculateDepositMonotonic(initial, y1, y2 - 1);
        calculateDepositIncreases(initial, y2 - 1);
    }
}

lemma calculateDepositGrowth(initial: int, years: int)
    requires initial > 0
    requires years >= 0
    ensures calculateDeposit(initial, years) >= initial
{
    if years == 0 {
    } else {
        calculateDepositGrowth(initial, years - 1);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(X: int) returns (years: int)
    requires X >= 101
    ensures years >= 0
    ensures var finalDeposit := calculateDeposit(100, years); finalDeposit >= X
    ensures years == 0 || calculateDeposit(100, years - 1) < X
// </vc-spec>
// <vc-code>
{
    years := 0;
    while calculateDeposit(100, years) < X
        invariant years >= 0
        invariant calculateDeposit(100, years) >= 100
        decreases X - calculateDeposit(100, years)
    {
        calculateDepositIncreases(100, years);
        years := years + 1;
    }
}
// </vc-code>

