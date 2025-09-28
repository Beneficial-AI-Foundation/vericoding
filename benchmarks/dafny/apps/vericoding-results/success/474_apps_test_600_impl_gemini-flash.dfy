// <vc-preamble>
predicate ValidInput(a: int, b: int)
{
    a >= 1 && a <= 1000 && b >= 1 && b <= 1000 && a != b
}

function OptimalMeetingPoint(a: int, b: int): int
{
    (a + b) / 2
}

function MinimumTotalTiredness(a: int, b: int): int
    requires ValidInput(a, b)
{
    var c := OptimalMeetingPoint(a, b);
    tirednessForSteps(abs(c - a)) + tirednessForSteps(abs(b - c))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): add abs function */
function abs(x: int): int {
  if x < 0 then -x else x
}

function tirednessForSteps(steps: int): int
{
    if steps <= 0 then 0
    else steps * (steps + 1) / 2
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: int)
    requires ValidInput(a, b)
    ensures result >= 0
    ensures result == MinimumTotalTiredness(a, b)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): calculate tiredness based on optimal meeting point */
{
  var c := OptimalMeetingPoint(a, b);
  result := tirednessForSteps(abs(c - a)) + tirednessForSteps(abs(b - c));
}
// </vc-code>
