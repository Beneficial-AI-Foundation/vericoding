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

function SumWithDecreasingPowers(n: int, power: int): int
    requires n >= 1
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

function SumWithIncreasingPowers(n: int, power: int): int
    requires n >= 1
    requires power >= 1
    decreases n
{
    if n == 0 then 0
    else 
        var count := n / power;
        var remainder := n % power;
        count + SumWithIncreasingPowers(remainder, power * 2)
}

lemma PowerProperty(l: int, r: int)
    requires l >= 0 && r >= 0
    ensures Power(2, l) * Power(2, r) == Power(2, l + r)

lemma DecreasingPowersLemma(n: int, power: int)
    requires n >= 0
    requires power >= 1
    ensures SumWithDecreasingPowers(n, power) >= n / power

lemma IncreasingPowersLemma(n: int, power: int)
    requires n >= 0
    requires power >= 1
    ensures SumWithIncreasingPowers(n, power) >= n / power
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
    var current_power := 1;
    max_sum := 0;
    var current_n := n;
    var power_count := r;
    
    while power_count > 0 && current_n > 0
        invariant current_n >= 0
        invariant max_sum >= 0
        decreases power_count, current_n
    {
        var power_value := Power(2, power_count - 1);
        var count := current_n / power_value;
        max_sum := max_sum + count;
        current_n := current_n % power_value;
        power_count := power_count - 1;
    }
    
    min_sum := 0;
    current_n := n;
    var current_divisor := Power(2, l - 1);
    
    while current_n > 0 && current_divisor >= 1
        invariant current_n >= 0
        invariant min_sum >= 0
        decreases current_n, current_divisor
    {
        var count := current_n / current_divisor;
        min_sum := min_sum + count;
        current_n := current_n % current_divisor;
        current_divisor := current_divisor / 2;
    }
}
// </vc-code>

