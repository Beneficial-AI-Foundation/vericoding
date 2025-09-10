predicate ValidInput(x: int)
{
  x >= 1
}

predicate IsMinimalSteps(x: int, steps: int)
  requires x >= 1
{
  steps >= 1 &&
  steps * 5 >= x &&
  (steps - 1) * 5 < x
}

// <vc-helpers>
function method DivideCeil(x: int, y: int): int
  requires y > 0
  ensures DivideCeil(x, y) * y >= x
  ensures (DivideCeil(x, y) - 1) * y < x
  ensures (x % y == 0) ==> (DivideCeil(x, y) == x / y)
{
  (x + y - 1) / y
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  return DivideCeil(x, 5);
}
// </vc-code>

