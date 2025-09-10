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

function SumWithDecreasingPowers(n: int, start_power: int): int
  requires n >= 0
{
  n * start_power + n * (n - 1) / 2
}

function SumWithIncreasingPowers(n: int, max_power: int): int
  requires n >= 0
{
  n * (max_power * 2) - n * (n + 1) / 2
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
  var min_pow := Power(2, l - 1);
  var max_pow := Power(2, r - 1);
  min_sum := n * min_pow + n * (n - 1) / 2;
  max_sum := n * (max_pow * 2) - n * (n + 1) / 2;
}
// </vc-code>

