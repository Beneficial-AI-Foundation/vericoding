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
lemma PowerLemma(base: int, exp: int)
  requires exp >= 0
  ensures Power(base, exp) == if exp == 0 then 1 else base * Power(base, exp - 1)
{
}

lemma PowerPositive(base: int, exp: int)
  requires exp >= 0
  requires base >= 0
  ensures Power(base, exp) >= 0
{
  if exp > 0 {
    PowerPositive(base, exp - 1);
  }
}

lemma PowerZeroNonNegativeBase(base: int, exp: nat)
  requires base >= 0
  ensures Power(base, exp) >= 0
{
  if exp > 0 {
    PowerZeroNonNegativeBase(base, exp - 1);
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
  if n == 1 {
    result := k;
  } else {
    var ways: int := k;
    var remaining: int := k - 1;
    var count: int := n - 1;
    
    while count > 0
      invariant count >= 0
      invariant ways == k * Power(remaining, n - count - 1)
      invariant ways > 0
    {
      ways := ways * remaining;
      count := count - 1;
      
      assert ways == k * Power(remaining, n - count - 1);
    }
    
    result := ways;
  }
}
// </vc-code>

