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

// <vc-helpers>
function abs(i: int): int {
  if i >= 0 then i else -i
}

function tirednessForSteps(n: int): int {
  if n <= 0 then 0 else n * (n + 1) / 2
}

lemma AbsNonNeg(i: int)
  ensures abs(i) >= 0
{}

lemma TirednessNonNeg(n: int)
  ensures tirednessForSteps(n) >= 0
{}

lemma MinimumTotalTirednessNonNeg(a: int, b: int)
  requires ValidInput(a, b)
  ensures MinimumTotalTiredness(a, b) >= 0
{
  AbsNonNeg(OptimalMeetingPoint(a, b) - a);
  AbsNonNeg(b - OptimalMeetingPoint(a, b));
  TirednessNonNeg(abs(OptimalMeetingPoint(a, b) - a));
  TirednessNonNeg(abs(b - OptimalMeetingPoint(a, b)));
  assert MinimumTotalTiredness(a, b) ==
    tirednessForSteps(abs(OptimalMeetingPoint(a, b) - a)) +
    tirednessForSteps(abs(b - OptimalMeetingPoint(a, b)));
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: int)
    requires ValidInput(a, b)
    ensures result >= 0
    ensures result == MinimumTotalTiredness(a, b)
// </vc-spec>
// <vc-code>
{
  result := MinimumTotalTiredness(a, b);
  MinimumTotalTirednessNonNeg(a, b);
}
// </vc-code>

