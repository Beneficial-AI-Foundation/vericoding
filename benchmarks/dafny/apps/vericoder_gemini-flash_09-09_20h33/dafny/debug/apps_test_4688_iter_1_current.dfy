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
function Power(base: int, exp: int): int
  requires exp >= 0
  ensures Power(base, exp) >= 0 // Add a postcondition to ensure non-negativity
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
  ensures PaintingWays(n, k) > 0 // Ensure the result is positive
{
  k * Power(k - 1, n - 1)
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
    invariant res == k * Power(k - 1, i - 1) // Invariant to track the calculation of PaintingWays
  {
    res := res * (k - 1);
    i := i + 1;
  }
  return res;
}
// </vc-code>

