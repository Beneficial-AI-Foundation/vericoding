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
  ensures (base == 0 && exp == 0) ==> (Power(base, exp) == 1) // 0^0 is 1
  ensures (base == 0 && exp > 0) ==> (Power(base, exp) == 0) // 0^pos is 0
  ensures (base != 0 && exp == 0) ==> (Power(base, exp) == 1) // x^0 is 1
  ensures (base > 0 && exp > 0) ==> (Power(base, exp) > 0) // pos^pos is pos
  ensures (base < 0 && exp > 0 && exp % 2 == 0) ==> (Power(base, exp) > 0) // neg^even is pos
  ensures (base < 0 && exp > 0 && exp % 2 != 0) ==> (Power(base, exp) < 0) // neg^odd is neg
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
  ensures PaintingWays(n, k) == k * Power(k - 1, n - 1) // Define the function explicitly
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
    invariant res == k * Power(k - 1, i - 1)
    decreases n - i
  {
    res := res * (k - 1);
    i := i + 1;
  }
  return res;
}
// </vc-code>

