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
// No additional helpers needed
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  steps := (x + 4) / 5;
}
// </vc-code>

