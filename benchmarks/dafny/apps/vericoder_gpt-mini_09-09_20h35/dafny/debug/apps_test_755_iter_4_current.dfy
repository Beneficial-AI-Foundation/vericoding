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
lemma InitInvariant(x: int)
  requires x >= 1
  ensures (1 - 1) * 5 < x
{
  assert 0 < x;
}

lemma MetricDecreases(x: int, steps: int)
  requires x >= 1
  requires steps >= 1
  ensures x - steps * 5 < x - (steps - 1) * 5
{
  assert steps * 5 > (steps - 1) * 5;
  assert x - steps * 5 < x - (steps - 1) * 5;
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  steps := 1;
  InitInvariant(x);
  while steps * 5 < x
    decreases x - (steps - 1) * 5
    invariant steps >= 1
    invariant (steps - 1) * 5 < x
  {
    MetricDecreases(x, steps);
    steps := steps + 1;
  }
}
// </vc-code>

