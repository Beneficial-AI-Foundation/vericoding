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
function tirednessForSteps(n: int): int
{
  n * (n + 1) / 2
}

lemma OptimalMeetingPointMinimizesTiredness(a: int, b: int)
  requires ValidInput(a, b)
  ensures MinimumTotalTiredness(a, b) == tirednessForSteps((abs(b - a) + 1) / 2) + tirednessForSteps(abs(b - a) / 2)
{
  var diff := abs(b - a);
  var c := (a + b) / 2;
  
  // The optimal meeting point splits the distance in such a way that
  // we get the minimum sum of triangular numbers
  if diff % 2 == 0 {
    // Even distance: both get diff/2 steps
    assert tirednessForSteps(diff / 2) * 2 == MinimumTotalTiredness(a, b);
  } else {
    // Odd distance: one gets (diff+1)/2, the other gets (diff-1)/2
    var n1 := (diff + 1) / 2;
    var n2 := (diff - 1) / 2;
    assert tirednessForSteps(n1) + tirednessForSteps(n2) == MinimumTotalTiredness(a, b);
  }
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
  var diff := abs(b - a);
  var half := diff / 2;
  
  if diff % 2 == 0 {
    result := half * (half + 1);
  } else {
    var n1 := (diff + 1) / 2;
    var n2 := n1 - 1;
    result := (n1 * (n1 + 1)) / 2 + (n2 * (n2 + 1)) / 2;
  }
}
// </vc-code>

