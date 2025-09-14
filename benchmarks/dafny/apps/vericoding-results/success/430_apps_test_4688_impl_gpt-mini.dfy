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
lemma Power_ge_one(b: int, e: int)
  requires b >= 1 && e >= 0
  ensures Power(b, e) >= 1
{
  if e == 0 {
    assert Power(b, 0) == 1;
  } else {
    Power_ge_one(b, e - 1);
    assert Power(b, e) == b * Power(b, e - 1);
    // b >= 1 and Power(b, e-1) >= 1 imply product >= 1
    assert b * Power(b, e - 1) >= 1;
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
  var res := k;
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant res == k * Power(k - 1, i - 1)
    decreases n - i
  {
    res := res * (k - 1);
    i := i + 1;
  }
  result := res;
  // Use lemma to establish positivity
  Power_ge_one(k - 1, n - 1);
  assert result == PaintingWays(n, k);
  assert result > 0;
}
// </vc-code>

