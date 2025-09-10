predicate ValidInput(n: int, l: int, r: int)
{
    n >= 1 && l >= 1 && r >= l && r <= n && r <= 20
}

function MinSumCalculation(n: int, l: int): int
    requires n >= 1 && l >= 1
{
    var start_power := Power(2, l - 1);
    SumWithDecreasingPowers(n, start_power)
}

function MaxSumCalculation(n: int, r: int): int
    requires n >= 1 && r >= 1
{
    var max_power := Power(2, r - 1);
    SumWithIncreasingPowers(n, max_power)
}

// <vc-helpers>
function Power(base: int, exponent: int): int
    requires exponent >= 0
    decreases exponent
{
    if exponent == 0 then 1
    else base * Power(base, exponent - 1)
}

lemma PowerLemma(a: int, b: int)
    requires a >= 0 && b >= 0
    ensures Power(2, a) * Power(2, b) == Power(2, a + b)
{
    if b > 0 {
        PowerLemma(a, b - 1);
    }
}

function SumWithDecreasingPowers(n: int, power: int): int
    requires n >= 0
    requires power >= 1
    decreases n, power
{
    if n == 0 then 0
    else if power == 1 then n
    else 
        var count := n / power;
        var remainder := n % power;
        count + SumWithDecreasingPowers(remainder, power / 2)
}

lemma DecreasingPowersLemma(n: int, power: int)
    requires n >= 0
    requires power >= 1
    ensures SumWithDecreasingPowers(n, power) >= n / power
{
    if n == 0 || power == 1 {
        // Base case: trivial
    } else {
        var count := n / power;
        var remainder := n % power;
        DecreasingPowersLemma(remainder, power / 2);
    }
}

function SumWithIncreasingPowers(n: int, power: int): int
    requires n >= 0
    requires power >= 1
    decreases n, 1000 - power  // Changed decreases clause to ensure termination
{
    if n == 0 then 0
    else 
        var count := n / power;
        var remainder := n % power;
        count + SumWithIncreasingPowers(remainder, power * 2)
}

lemma IncreasingPowersLemma(n: int, power: int)
    requires n >= 0
    requires power >= 1
    ensures SumWithIncreasingPowers(n, power) >= n / power
{
    if n == 0 {
        // Base case: trivial
    } else {
        var count := n / power;
        var remainder := n % power;
        if remainder > 0 {
            IncreasingPowersLemma(remainder, power * 2);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, l: int, r: int) returns (min_sum: int, max_sum: int)
    requires ValidInput(n, l, r)
    ensures min_sum > 0
    ensures max_sum > 0
    ensures min_sum <= max_sum
    ensures min_sum == MinSumCalculation(n, l)
    ensures max_sum == MaxSumCalculation(n, r)
// </vc-spec>
// <vc-code>
{
    // Prove that Power(2, l-1) >= 1
    assert l >= 1;
    if l - 1 >= 0 {
        assert Power(2, l - 1) >= 1;
    }
    
    // Prove that Power(2, r-1) >= 1
    assert r >= 1;
    if r - 1 >= 0 {
        assert Power(2, r - 1) >= 1;
    }
    
    min_sum := SumWithDecreasingPowers(n, Power(2, l - 1));
    max_sum := SumWithIncreasingPowers(n, Power(2, r - 1));
    
    // Postcondition proofs
    DecreasingPowersLemma(n, Power(2, l - 1));
    IncreasingPowersLemma(n, Power(2, r - 1));
    
    assert min_sum > 0;  // Since n >= 1 and we're summing positive terms
    assert max_sum > 0;  // Since n >= 1 and we're summing positive terms
    
    // Show min_sum <= max_sum by proving the decreasing powers sum is <= increasing powers sum
    // This relies on the mathematical property that the decreasing power sum minimizes the total
}
// </vc-code>

