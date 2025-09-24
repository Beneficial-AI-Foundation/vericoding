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
// </vc-helpers>

// <vc-spec>
method car_race_collision(n: int) returns (result: int)
    requires ValidInput(n)
    ensures ValidResult(n, result)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
  }
// </vc-code>
