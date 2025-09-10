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
method ComputeDistanceToHouse(n: int, a: int) returns (result: int)
  requires ValidInput(n, a)
  ensures result == DistanceToHouse(n, a)
  ensures result > 0
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  if a % 2 == 1 {
    result := a / 2 + 1;
  } else {
    result := (n - a) / 2 + 1;
  }
}
// </vc-code>

