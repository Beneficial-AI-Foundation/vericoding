predicate ValidInput(n: int, a: int)
{
  n > 0 && n % 2 == 0 && 1 <= a <= n
}

function DistanceToHouse(n: int, a: int): int
  requires ValidInput(n, a)
  ensures DistanceToHouse(n, a) > 0
{
  if a % 2 == 1 then
    a / 2 + 1
  else
    (n - a) / 2 + 1
}

// <vc-helpers>
method ComputeDistance(n: int, a: int) returns (d: int)
  requires ValidInput(n, a)
  ensures d == DistanceToHouse(n, a)
{
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
d := DistanceToHouse(n, a);
}
// </vc-code>

