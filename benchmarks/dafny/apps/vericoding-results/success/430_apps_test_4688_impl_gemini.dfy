function Power(base: int, exp: int): int
  requires exp >= 0
{
  if exp == 0 then 1
  else base * Power(base, exp - 1)
}

predicate ValidInput(n: int, k: int)
{
  1 <= n <= 1000 && 2 <= k <= 1000
}

function PaintingWays(n: int, k: int): int
  requires ValidInput(n, k)
{
  k * Power(k - 1, n - 1)
}

// <vc-helpers>
lemma PowerPositive(base: int, exp: int)
  requires base >= 1
  requires exp >= 0
  ensures Power(base, exp) >= 1
  decreases exp
{
  if exp > 0 {
    PowerPositive(base, exp - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
  requires ValidInput(n, k)
  ensures result == PaintingWays(n, k)
  ensures result > 0
// </vc-spec>
// <vc-code>
{
  var power_val := 1;
  var i := 0;
  while i < n - 1
    decreases n - 1 - i
    invariant 0 <= i <= n - 1
    invariant power_val == Power(k - 1, i)
  {
    power_val := power_val * (k - 1);
    i := i + 1;
  }
  result := k * power_val;
  PowerPositive(k - 1, n - 1);
}
// </vc-code>

