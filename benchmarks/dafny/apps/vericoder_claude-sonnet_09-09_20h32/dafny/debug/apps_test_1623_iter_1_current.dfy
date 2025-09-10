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
function Power(base: int, exp: int): int
    requires base >= 0 && exp >= 0
    ensures Power(base, exp) >= 1 || (base == 0 && exp > 0)
    decreases exp
{
    if exp == 0 then 1
    else base * Power(base, exp - 1)
}

function SumWithDecreasingPowers(n: int, start_power: int): int
    requires n >= 1 && start_power >= 1
    ensures SumWithDecreasingPowers(n, start_power) > 0
    decreases n
{
    if n == 1 then start_power
    else start_power + SumWithDecreasingPowers(n - 1, start_power / 2)
}

function SumWithIncreasingPowers(n: int, max_power: int): int
    requires n >= 1 && max_power >= 1
    ensures SumWithIncreasingPowers(n, max_power) > 0
    decreases n
{
    if n == 1 then max_power
    else max_power + SumWithIncreasingPowers(n - 1, max_power / 2)
}

lemma PowerPositive(base: int, exp: int)
    requires base >= 2 && exp >= 0
    ensures Power(base, exp) >= 1
    decreases exp
{
    if exp == 0 {
        assert Power(base, exp) == 1;
    } else {
        PowerPositive(base, exp - 1);
        assert Power(base, exp) == base * Power(base, exp - 1);
        assert Power(base, exp) >= 2 * 1;
    }
}

lemma MinMaxRelation(n: int, l: int, r: int)
    requires ValidInput(n, l, r)
    ensures MinSumCalculation(n, l) <= MaxSumCalculation(n, r)
{
    PowerPositive(2, l - 1);
    PowerPositive(2, r - 1);
    assert l <= r;
    assert Power(2, l - 1) <= Power(2, r - 1);
    SumMonotonic(n, Power(2, l - 1), Power(2, r - 1));
}

lemma SumMonotonic(n: int, p1: int, p2: int)
    requires n >= 1 && p1 >= 1 && p2 >= 1 && p1 <= p2
    ensures SumWithDecreasingPowers(n, p1) <= SumWithIncreasingPowers(n, p2)
    decreases n
{
    if n == 1 {
        assert SumWithDecreasingPowers(n, p1) == p1;
        assert SumWithIncreasingPowers(n, p2) == p2;
    } else {
        SumMonotonic(n - 1, p1 / 2, p2 / 2);
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
    PowerPositive(2, l - 1);
    PowerPositive(2, r - 1);
    
    min_sum := MinSumCalculation(n, l);
    max_sum := MaxSumCalculation(n, r);
    
    MinMaxRelation(n, l, r);
}
// </vc-code>

