// <vc-preamble>
predicate ValidInput(n: int)
{
    n >= 0
}

function CollisionCount(n: int): int
    requires ValidInput(n)
{
    n * n
}

predicate ValidResult(n: int, result: int)
    requires ValidInput(n)
{
    result == CollisionCount(n) && result >= 0
}
// </vc-preamble>

// <vc-helpers>
function ComputeCollision(n: int): int
  requires n >= 0
{
  if n == 0 then 0 else n * n
}
// </vc-helpers>

// <vc-spec>
method car_race_collision(n: int) returns (result: int)
    requires ValidInput(n)
    ensures ValidResult(n, result)
// </vc-spec>
// <vc-code>
{
  result := CollisionCount(n);
}
// </vc-code>
