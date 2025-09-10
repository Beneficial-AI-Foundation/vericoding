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
    if exponent == 0 then 1 else base * Power(base, exponent - 1)
}

function SumWithDecreasingPowers(n: int, start_power: int): int
    requires n >= 1 && start_power >= 0
    decreases n
{
    if n == 1 then start_power
    else start_power + SumWithDecreasingPowers(n - 1, start_power / 2)
}

function SumWithIncreasingPowers(n: int, max_power: int): int
    requires n >= 1 && max_power > 0
    decreases n
{
    if n == 1 then max_power
    else max_power + SumWithIncreasingPowers(n - 1, max_power * 2)
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
    min_sum := MinSumCalculation(n, l);
    max_sum := MaxSumCalculation(n, r);
}
// </vc-code>

