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
lemma DistanceToHousePositive(n: int, a: int)
  requires ValidInput(n, a)
  ensures DistanceToHouse(n, a) > 0
{
  if a % 2 == 1 {
    assert a >= 1;
    assert a / 2 + 1 >= 1;
  } else {
    assert a <= n;
    assert n >= 2;
    assert (n - a) / 2 + 1 >= 1;
  }
}

method CalculateDistance(n: int, a: int) returns (distance: int)
  requires ValidInput(n, a)
  ensures distance > 0
  ensures distance == DistanceToHouse(n, a)
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  distance := DistanceToHouse(n, a);
}
// </vc-code>

