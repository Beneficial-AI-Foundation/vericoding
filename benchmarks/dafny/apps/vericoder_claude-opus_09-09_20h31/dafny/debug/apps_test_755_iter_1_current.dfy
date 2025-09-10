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
method ComputeMinimalSteps(x: int) returns (steps: int)
  requires ValidInput(x)
  ensures IsMinimalSteps(x, steps)
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  steps := (x + 4) / 5;
}
// </vc-code>

