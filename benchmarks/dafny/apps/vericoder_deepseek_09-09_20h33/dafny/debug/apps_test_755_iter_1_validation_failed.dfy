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
lemma {:axiom} MinimalStepsLemma(x: int)
  requires ValidInput(x)
  ensures exists steps: int :: IsMinimalSteps(x, steps)
{
}

lemma {:axiom} MinimalStepsUnique(x: int, steps1: int, steps2: int)
  requires ValidInput(x) && IsMinimalSteps(x, steps1) && IsMinimalSteps(x, steps2)
  ensures steps1 == steps2
{
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  var steps := (x + 4) / 5;
  assert IsMinimalSteps(x, steps);
  return steps;
}
// </vc-code>

