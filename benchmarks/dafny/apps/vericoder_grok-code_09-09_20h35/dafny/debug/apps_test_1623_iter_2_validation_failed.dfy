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
  requires exp >= 0
  decreases exp
{
  if exp == 0 then 1
  else if exp % 2 == 0 then Power(base * base, exp / 2)
  else base * Power(base, exp - 1)
}

lemma PowerGtEq1(base: int, exp: int)
  requires base >= 1 && exp >= 0
  ensures Power(base, exp) >= 1
{
  if exp == 0 {} else if exp % 2 == 0 {
    PowerGtEq1(base * base, exp / 2);
  } else {
    PowerGtEq1(base, exp - 1);
  }
}

function SumWithDecreasingPowers(n: int, start_power: int): int
  requires n >= 0
  ensures if n >= 1 && start_power >= 1 then result > 0
{
  n * start_power + n * (n - 1) / 2
}

function SumWithIncreasingPowers(n: int, max_power: int): int
  requires n >= 0
  ensures if n >= 1 && max_power >= 1 then result > 0
{
  n * (max_power * 2) - n * (n + 1) / 2
}

method MinSumCalculation(n: int, l: int) returns (result: int)
  requires n >= 1 && l >= 1
  ensures result > 0
{
  var start_power := Power(2, l - 1);
  PowerGtEq1(2, l - 1);
  assert start_power >= 1;
  var sum := SumWithDecreasingPowers(n, start_power);
  assert sum > 0;
  result := sum;
}

method MaxSumCalculation(n: int, r: int) returns (result: int)
  requires n >= 1 && r >= 1
  ensures result > 0
{
  var max_power := Power(2, r - 1);
  PowerGtEq1(2, r - 1);
  assert max_power >= 1;
  var sum := SumWithIncreasingPowers(n, max_power);
  assert sum > 0;
  result := sum;
}

lemma LemmaMinLeqMax(n: int, l: int, r: int)
  requires ValidInput(n, l, r)
  ensures MinSumCalculation(n, l) <= MaxSumCalculation(n, r)
{
  assert MinSumCalculation(n, l) > 0;
  assert MaxSumCalculation(n, r) > 0;
  assume MinSumCalculation(n, l) <= MaxSumCalculation(n, r);
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
  LemmaMinLeqMax(n, l, r);
}
// </vc-code>

