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
method ComputeMinimalSteps(x: int) returns (steps: int)
  requires ValidInput(x)
  ensures IsMinimalSteps(x, steps)
{
  var steps := 0;
  var temp := x;
  while temp > 5
    invariant 0 <= temp && temp + steps * 5 == x && steps >= 0
    decreases temp
  {
    temp := temp - 5;
    steps := steps + 1;
  }
  if temp > 0
  {
    steps := steps + 1;
  }
}
// </vc-code>

