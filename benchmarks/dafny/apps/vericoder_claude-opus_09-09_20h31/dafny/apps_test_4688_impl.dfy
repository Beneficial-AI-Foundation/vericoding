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
lemma PowerMultiply(base: int, exp1: int, exp2: int)
  requires exp1 >= 0
  requires exp2 >= 0
  ensures Power(base, exp1) * Power(base, exp2) == Power(base, exp1 + exp2)
{
  if exp1 == 0 {
    assert Power(base, 0) == 1;
    assert 1 * Power(base, exp2) == Power(base, exp2);
  } else {
    PowerMultiply(base, exp1 - 1, exp2);
    assert Power(base, exp1) == base * Power(base, exp1 - 1);
    assert Power(base, exp1) * Power(base, exp2) == base * Power(base, exp1 - 1) * Power(base, exp2);
    assert base * Power(base, exp1 - 1) * Power(base, exp2) == base * Power(base, exp1 - 1 + exp2);
    assert base * Power(base, exp1 - 1 + exp2) == Power(base, exp1 + exp2);
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
    power := power * (k - 1);
    i := i + 1;
  }
  
  result := k * power;
  
  assert k >= 2;
  assert k - 1 >= 1;
  PowerPositive(k - 1, n - 1);
  assert Power(k - 1, n - 1) > 0;
  assert result > 0;
}
// </vc-code>

