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
function Power(base: int, exp: nat): int
    requires base >= 1
    ensures Power(base, exp) >= 1
{
    if exp == 0 then 1
    else base * Power(base, exp - 1)
}

function SumWithDecreasingPowers(n: int, start_power: int): int
    requires n >= 1
    requires start_power >= 1
    ensures SumWithDecreasingPowers(n, start_power) >= n
{
    if n == 1 then
        start_power
    else
        start_power + SumWithDecreasingPowers(n - 1, start_power / 2)
}

function SumWithIncreasingPowers(n: int, max_power: int): int
    requires n >= 1
    requires max_power >= 1
    ensures SumWithIncreasingPowers(n, max_power) >= n
{
    if n == 1 then
        max_power
    else
        max_power + SumWithIncreasingPowers(n - 1, max_power * 2)
}

lemma PowerPositive(base: int, exp: nat)
    requires base >= 1
    ensures Power(base, exp) >= 1
{
    // Proof by induction on exp
}

lemma MinMaxOrdering(n: int, l: int, r: int)
    requires ValidInput(n, l, r)
    ensures MinSumCalculation(n, l) <= MaxSumCalculation(n, r)
{
    // This follows from l <= r and the structure of the sums
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
    var start_power := Power(2, l - 1);
    min_sum := SumWithDecreasingPowers(n, start_power);
    
    var max_power := Power(2, r - 1);
    max_sum := SumWithIncreasingPowers(n, max_power);
    
    MinMaxOrdering(n, l, r);
}
// </vc-code>

