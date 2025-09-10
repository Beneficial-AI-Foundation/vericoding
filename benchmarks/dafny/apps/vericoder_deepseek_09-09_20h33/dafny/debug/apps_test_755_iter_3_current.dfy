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
lemma {:vcs_split_on_every_assert} MinimalStepsLemma(x: int, steps: int)
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
  var steps := (x + 4) / 5;
  assert steps >= 1;
  assert steps * 5 >= x;
  assert (steps - 1) * 5 < x;
}
// </vc-code>

