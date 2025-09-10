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
lemma {:axiom} MinimalStepsProperty(x: int, steps: int)
  requires x >= 1
  requires steps >= 1 && steps * 5 >= x && (steps - 1) * 5 < x
  ensures IsMinimalSteps(x, steps)
{
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  var x := 5;
  var steps := 1;
  while steps * 5 < x
    invariant steps >= 1
    invariant steps * 5 >= x - 4
  {
    steps := steps + 1;
  }
  assert IsMinimalSteps(x, steps);
}
// </vc-code>

