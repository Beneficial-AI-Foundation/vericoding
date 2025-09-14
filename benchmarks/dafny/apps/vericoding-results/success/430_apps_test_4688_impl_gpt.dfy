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
lemma Prod_pos(a: int, b: int)
  requires a > 0
  requires b > 0
  ensures a * b > 0
{
}

lemma Power_pos(base: int, exp: int)
  requires base >= 1
  requires exp >= 0
  ensures Power(base, exp) > 0
  decreases exp
{
  if exp == 0 {
    assert Power(base, 0) == 1;
  } else {
    assert exp - 1 >= 0;
    Power_pos(base, exp - 1);
    Prod_pos(base, Power(base, exp - 1));
    assert Power(base, exp) == base * Power(base, exp - 1);
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
  result := PaintingWays(n, k);
  assert result == k * Power(k - 1, n - 1);
  assert k >= 2;
  assert n >= 1;
  assert k - 1 >= 1;
  assert n - 1 >= 0;
  Power_pos(k - 1, n - 1);
  Prod_pos(k, Power(k - 1, n - 1));
  assert result > 0;
}
// </vc-code>

