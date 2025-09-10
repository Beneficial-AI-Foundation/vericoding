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
function calculateDeposit(initial: int, years: int): int
    requires initial >= 0
    requires years >= 0
    decreases years
{
    if years == 0 then initial
    else 
        var prevDeposit := calculateDeposit(initial, years - 1);
        prevDeposit + prevDeposit / 100
}

lemma lemma_deposit_increases(initial: int, years: int)
    requires initial >= 0
    requires years >= 0
    ensures calculateDeposit(initial, years + 1) > calculateDeposit(initial, years)
    decreases years
{
    if years == 0 {
        calc {
            calculateDeposit(initial, 1);
            calculateDeposit(initial, 0) + calculateDeposit(initial, 0) / 100;
            initial + initial / 100;
        }
        assert calculateDeposit(initial, 1) > calculateDeposit(initial, 0) by (calc { initial + initial / 100; initial; } assert initial >= 0 ==> initial + initial/100 > initial;);
    } else {
        lemma_deposit_increases(initial, years - 1);
        var prev_prev := calculateDeposit(initial, years - 1);
        var prev := calculateDeposit(initial, years);
        var curr := calculateDeposit(initial, years + 1);

        calc {
            curr;
            prev + prev / 100;
            { assert prev = prev_prev + prev_prev / 100; }
            (prev_prev + prev_prev / 100) + (prev_prev + prev_prev / 100) / 100;
        }
        calc {
            prev;
            prev_prev + prev_prev / 100;
        }
        assert curr > prev by (calc { prev + prev/100; prev; } assert prev >= 0 ==> prev + prev/100 > prev;); // proof needed prev >= 0
        assert calculateDeposit(initial, years) >= 0; // follows from function definition
    }
}

lemma lemma_deposit_upper_bound(X: int, initial: int, years: int)
    requires X >= 1
    requires initial >= 0
    requires calculateDeposit(initial, years - 1) < X
    ensures years == 0 || calculateDeposit(initial, years - 1) < X
    decreases years
{
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
        lemma_deposit_increases(100, years);
        years := years + 1;
    }
}
// </vc-code>

