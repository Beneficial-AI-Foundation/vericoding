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
lemma PowerIterative(base: int, exp: int, acc: int, i: int)
  requires exp >= 0
  requires 0 <= i <= exp
  ensures acc * Power(base, exp - i) == Power(base, exp - i) * acc
  ensures Power(base, i) * Power(base, exp - i) == Power(base, exp)
{
  if i == 0 {
    assert Power(base, 0) == 1;
  } else if i < exp {
    PowerIterative(base, exp, acc * base, i + 1);
    assert Power(base, i + 1) == base * Power(base, i);
  }
}

lemma PowerPositive(base: int, exp: int)
  requires base > 0
  requires exp >= 0
  ensures Power(base, exp) > 0
{
  if exp == 0 {
    assert Power(base, 0) == 1;
  } else {
    PowerPositive(base, exp - 1);
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
  var power := 1;
  var i := 0;
  
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant power == Power(k - 1, i)
  {
    PowerIterative(k - 1, i, power, 0);
    power := power * (k - 1);
    i := i + 1;
  }
  
  assert power == Power(k - 1, n - 1);
  result := k * power;
  assert result == k * Power(k - 1, n - 1);
  assert result == PaintingWays(n, k);
  
  // Prove result > 0
  assert k >= 2;
  assert k - 1 >= 1;
  PowerPositive(k - 1, n - 1);
  assert Power(k - 1, n - 1) > 0;
  assert result == k * Power(k - 1, n - 1);
  assert result > 0;
}
// </vc-code>

