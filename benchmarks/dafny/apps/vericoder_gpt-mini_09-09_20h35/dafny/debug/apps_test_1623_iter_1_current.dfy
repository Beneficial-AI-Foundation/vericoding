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
function Power(b: int, e: int): int
    requires b == 2 && e >= 0
    decreases e
{
    if e == 0 then 1 else 2 * Power(2, e - 1)
}

function SumWithDecreasingPowers(n: int, start_power: int): int
    requires n >= 1 && start_power >= 0
    decreases n
{
    if n == 1 then start_power else start_power + SumWithDecreasingPowers(n - 1, start_power / 2)
}

function SumWithIncreasingPowers(n: int, max_power: int): int
    requires n >= 1 && max_power >= 0
    decreases n
{
    if n == 1 then max_power else max_power + SumWithIncreasingPowers(n - 1, max_power * 2)
}

lemma PowerPositive(e: int)
    requires e >= 0
    ensures Power(2, e) >= 1
    decreases e
{
    if e == 0 {
    } else {
        PowerPositive(e - 1);
    }
}

lemma PowerMonotone(e1: int, e2: int)
    requires 0 <= e1 <= e2
    ensures Power(2, e1) <= Power(2, e2)
    decreases e2 - e1
{
    if e1 == e2 {
    } else {
        // e1 < e2, so e1 <= e2-1
        PowerMonotone(e1, e2 - 1);
        // Power(2, e2) = 2 * Power(2, e2-1) and Power(2, e2-1) >= Power(2, e1)
        // hence Power(2, e1) <= Power(2, e2)
    }
}

lemma SumWithDecreasingPositive(n: int, p: int)
    requires n >= 1 && p >= 1
    ensures SumWithDecreasingPowers(n, p) >= 1
    decreases n
{
    if n == 1 {
    } else {
        // Sum = p + rest >= p >= 1
        SumWithDecreasingPositive(n - 1, p / 2);
    }
}

lemma SumWithIncreasingPositive(n: int, p: int)
    requires n >= 1 && p >= 1
    ensures SumWithIncreasingPowers(n, p) >= 1
    decreases n
{
    if n == 1 {
    } else {
        SumWithIncreasingPositive(n - 1, p * 2);
    }
}

lemma SumWithDecreasingLeqSumWithIncreasing(n: int, a: int, b: int)
    requires n >= 1 && 0 <= a <= b
    ensures SumWithDecreasingPowers(n, a) <= SumWithIncreasingPowers(n, b)
    decreases n
{
    if n == 1 {
        // a <= b
    } else {
        // Show a + S_dec(n-1, a/2) <= b + S_inc(n-1, b*2)
        // Need 0 <= a/2 <= b*2 to apply IH
        SumWithDecreasingLeqSumWithIncreasing(n - 1, a / 2, b * 2);
        // Then use a <= b to conclude the full inequality
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
  min_sum := MinSumCalculation(n, l);
  max_sum := MaxSumCalculation(n, r);

  // Prove positivity of min_sum and max_sum
  PowerPositive(l - 1);
  SumWithDecreasingPositive(n, Power(2, l - 1));
  PowerPositive(r - 1);
  SumWithIncreasingPositive(n, Power(2, r - 1));

  // Prove min_sum <= max_sum
  PowerMonotone(l - 1, r - 1);
  SumWithDecreasingLeqSumWithIncreasing(n, Power(2, l - 1), Power(2, r - 1));
}
// </vc-code>

