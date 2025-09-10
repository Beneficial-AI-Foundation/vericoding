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
lemma calculateDepositIncreasing(initial: int, years: int)
    requires initial >= 0
    requires years >= 0
    ensures calculateDeposit(initial, years) >= initial
{
    if years == 0 {
        // Base case: calculateDeposit(initial, 0) == initial
    } else {
        calculateDepositIncreasing(initial, years - 1);
        var prev := calculateDeposit(initial, years - 1);
        assert prev >= initial;
        assert calculateDeposit(initial, years) == prev + prev / 100;
        assert prev >= 0;
        assert prev / 100 >= 0;
    }
}

lemma calculateDepositMonotonic(initial: int, y1: int, y2: int)
    requires initial >= 0
    requires 0 <= y1 <= y2
    ensures calculateDeposit(initial, y1) <= calculateDeposit(initial, y2)
{
    if y1 == y2 {
        // Base case: equal years means equal deposits
    } else {
        calculateDepositMonotonic(initial, y1, y2 - 1);
        var prev := calculateDeposit(initial, y2 - 1);
        assert calculateDeposit(initial, y2) == prev + prev / 100;
        calculateDepositIncreasing(initial, y2 - 1);
        assert prev >= 0;
        assert prev / 100 >= 0;
        assert calculateDeposit(initial, y2) >= prev;
        assert calculateDeposit(initial, y1) <= prev;
    }
}

lemma calculateDepositAtLeast100(years: int)
    requires years >= 0
    ensures calculateDeposit(100, years) >= 100
{
    calculateDepositIncreasing(100, years);
}

lemma calculateDepositGrows(initial: int, years: int)
    requires initial >= 100
    requires years > 0
    ensures calculateDeposit(initial, years) > calculateDeposit(initial, years - 1)
{
    var prev := calculateDeposit(initial, years - 1);
    calculateDepositIncreasing(initial, years - 1);
    assert prev >= initial;
    assert prev >= 100;
    assert prev / 100 >= 1;
    assert calculateDeposit(initial, years) == prev + prev / 100;
    assert calculateDeposit(initial, years) >= prev + 1;
    assert calculateDeposit(initial, years) > prev;
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
    var current := 100;
    
    while current < X
        invariant years >= 0
        invariant current == calculateDeposit(100, years)
        invariant current >= 100
        invariant years == 0 || calculateDeposit(100, years - 1) < X
    {
        var oldCurrent := current;
        current := current + current / 100;
        years := years + 1;
        
        assert oldCurrent == calculateDeposit(100, years - 1);
        assert current == oldCurrent + oldCurrent / 100;
        assert current == calculateDeposit(100, years);
        assert calculateDeposit(100, years - 1) == oldCurrent < X;
        
        calculateDepositAtLeast100(years);
        assert current >= 100;
    }
    
    assert current >= X;
    assert current == calculateDeposit(100, years);
}
// </vc-code>

