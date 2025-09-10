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
function calculateDeposit_func(initial: int, years: int): int
    requires initial >= 0
    requires years >= 0
    decreases years
{
    if years == 0 then initial
    else 
        var prevDeposit := calculateDeposit_func(initial, years - 1);
        prevDeposit + prevDeposit / 100
}

lemma lemma_deposit_increases(initial: int, years: int)
    requires initial >= 0
    requires years >= 0
    ensures calculateDeposit_func(initial, years + 1) > calculateDeposit_func(initial, years)
    decreases years
{
    if years == 0 {
        calc {
            calculateDeposit_func(initial, 1);
            { assert initial >= 0; } // Needed for initial + initial / 100 to be >= initial thus strictly greater if initial > 0
            initial + initial / 100;
        }
    } else {
        lemma_deposit_increases(initial, years - 1);
        var prev := calculateDeposit_func(initial, years);
        var curr := calculateDeposit_func(initial, years + 1);

        calc {
            curr;
            prev + prev / 100;
        }
        assert calculateDeposit_func(initial, years) >= 0; // follows from function definition
    }
}

lemma lemma_deposit_at_least_initial(initial: int, years: int)
    requires initial >= 0
    requires years >= 0
    ensures calculateDeposit_func(initial, years) >= initial
    decreases years
{
    if years == 0 {
        // calculateDeposit_func(initial, 0) == initial, so initial >= initial holds.
    } else {
        lemma_deposit_at_least_initial(initial, years - 1);
        var prevDeposit := calculateDeposit_func(initial, years - 1);
        assert calculateDeposit_func(initial, years) == prevDeposit + prevDeposit / 100;
        assert prevDeposit >= initial; // from lemma_deposit_at_least_initial(initial, years - 1)
        assert prevDeposit + prevDeposit / 100 >= prevDeposit;
        assert prevDeposit + prevDeposit / 100 >= initial;
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
    while calculateDeposit_func(100, years) < X
        invariant years >= 0
        invariant calculateDeposit_func(100, years) >= 100
        invariant forall k :: 0 <= k < years ==> calculateDeposit_func(100, k) < X
        decreases (X - calculateDeposit_func(100, years))
    {
        lemma_deposit_at_least_initial(100, years);
        lemma_deposit_increases(100, years);
        years := years + 1;
    }
}
// </vc-code>

