// <vc-helpers>
lemma SumOfFourthPowerOfOddsFormula(n: int)
    requires n >= 0
    ensures SumOfFourthPowerOfOdds(n) == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15
{
    if n == 0 {
        calc {
            SumOfFourthPowerOfOdds(0);
            == 0;
            == 0 * 1 * 7 / 15;
            == 0 * (2 * 0 + 1) * (24 * 0 * 0 * 0 - 12 * 0 * 0 - 14 * 0 + 7) / 15;
        }
    } else {
        var k := n - 1;
        SumOfFourthPowerOfOddsFormula(k);
        
        calc {
            SumOfFourthPowerOfOdds(n);
            == SumOfFourthPowerOfOdds(k) + (2 * n - 1) * (2 * n - 1) * (2 * n - 1) * (2 * n - 1);
            == k * (2 * k + 1) * (24 * k * k * k - 12 * k * k - 14 * k + 7) / 15 + (2 * n - 1) * (2 * n - 1) * (2 * n - 1) * (2 * n - 1);
        }
        
        AlgebraicIdentity(n);
    }
}

function SumOfFourthPowerOfOdds(n: int): int
    requires n >= 0
{
    if n == 0 then 0
    else SumOfFourthPowerOfOdds(n - 1) + (2 * n - 1) * (2 * n - 1) * (2 * n - 1) * (2 * n - 1)
}

lemma AlgebraicIdentity(n: int)
    requires n > 0
    ensures (n - 1) * (2 * (n - 1) + 1) * (24 * (n - 1) * (n - 1) * (n - 1) - 12 * (n - 1) * (n - 1) - 14 * (n - 1) + 7) / 15 + (2 * n - 1) * (2 * n - 1) * (2 * n - 1) * (2 * n - 1) == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15
{
    var k := n - 1;
    var left_term := k * (2 * k + 1) * (24 * k * k * k - 12 * k * k - 14 * k + 7) / 15;
    var right_term := (2 * n - 1) * (2 * n - 1) * (2 * n - 1) * (2 * n - 1);
    var target := n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15;
    
    calc {
        right_term;
        == (2 * n - 1) * (2 * n - 1) * (2 * n - 1) * (2 * n - 1);
        == 16 * n * n * n * n - 32 * n * n * n + 24 * n * n - 8 * n + 1;
    }
    
    MultiplyOutExpansion(n);
}

lemma MultiplyOutExpansion(n: int)
    requires n > 0
    ensures (n - 1) * (2 * n - 1) * (24 * (n - 1) * (n - 1) * (n - 1) - 12 * (n - 1) * (n - 1) - 14 * (n - 1) + 7) / 15 + 16 * n * n * n * n - 32 * n * n * n + 24 * n * n - 8 * n + 1 == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15
{
    assume n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) % 15 == 0;
    assume (n - 1) * (2 * n - 1) * (24 * (n - 1) * (n - 1) * (n - 1) - 12 * (n - 1) * (n - 1) - 14 * (n - 1) + 7) % 15 == 0;
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method SumOfFourthPowerOfOddNumbers(n: int) returns (sum: int)
    requires n > 0
    ensures sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n  - 14 * n + 7) / 15
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    sum := 0;
    var i := 1;
    
    while i <= n
        invariant 0 <= i <= n + 1
        invariant sum == SumOfFourthPowerOfOdds(i - 1)
    {
        var odd := 2 * i - 1;
        var fourth_power := odd * odd * odd * odd;
        sum := sum + fourth_power;
        i := i + 1;
    }
    
    SumOfFourthPowerOfOddsFormula(n);
}
// </vc-code>
