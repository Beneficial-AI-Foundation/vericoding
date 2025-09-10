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
function abs(x: int): int
{
  if x < 0 then -x else x
}

function tirednessForSteps(n: int): int
{
  n * (n + 1) / 2
}

lemma OptimalMeetingPointMinimizesTiredness(a: int, b: int)
  requires ValidInput(a, b)
  ensures MinimumTotalTiredness(a, b) == tirednessForSteps((abs(b - a) + 1) / 2) + tirednessForSteps(abs(b - a) / 2)
{
  var diff := abs(b - a);
  
  if diff % 2 == 0 {
    // Even case
    assert tirednessForSteps(diff / 2) + tirednessForSteps(diff / 2) == MinimumTotalTiredness(a, b);
  } else {
    // Odd case
    var n1 := (diff + 1) / 2;
    var n2 := (diff - 1) / 2;
    assert tirednessForSteps(n1) + tirednessForSteps(n2) == MinimumTotalTiredness(a, b);
  }
}

lemma tirednessAlgebra(n: int)
  ensures tirednessForSteps(n) == n * (n + 1) / 2
{
}

lemma EvenCaseTiredness(diff: int)
  requires diff % 2 == 0
  ensures tirednessForSteps(diff / 2) * 2 == (diff / 2) * (diff / 2 + 1)
{
  var half := diff / 2;
  tirednessAlgebra(half);
  calc {
    tirednessForSteps(half) * 2;
    == { tirednessAlgebra(half); }
    (half * (half + 1) / 2) * 2;
    == {}
    half * (half + 1);
  }
}

lemma OddCaseTiredness(diff: int)
  requires diff % 2 == 1
  ensures tirednessForSteps((diff + 1) / 2) + tirednessForSteps((diff - 1) / 2) == 
          ((diff + 1) / 2) * ((diff + 3) / 2) / 2 + ((diff - 1) / 2) * ((diff + 1) / 2) / 2
{
  var n1 := (diff + 1) / 2;
  var n2 := (diff - 1) / 2;
  tirednessAlgebra(n1);
  tirednessAlgebra(n2);
}

lemma OddCaseSimplified(diff: int)
  requires diff % 2 == 1
  ensures tirednessForSteps((diff + 1) / 2) + tirednessForSteps((diff - 1) / 2) == n1 * n1
  {
    var n1 := (diff + 1) / 2;
    var n2 := n1 - 1;
    tirednessAlgebra(n1);
    tirednessAlgebra(n2);
    calc {
      tirednessForSteps(n1) + tirednessForSteps(n2);
      == {}
      (n1 * (n1 + 1)) / 2 + (n2 * (n2 + 1)) / 2;
      == { assert n2 == n1 - 1; }
      (n1 * (n1 + 1)) / 2 + ((n1 - 1) * n1) / 2;
      == {}
      (n1*(n1 + 1) + n1*(n1 - 1)) / 2;
      == {}
      (n1*(n1 + 1 + n1 - 1)) / 2;
      == {}
      (n1*(2*n1)) / 2;
      == {}
      n1*n1;
    }
  }
// </vc-helpers>
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
  
  if diff % 2 == 0 {
    var half := diff / 2;
    result := half * (half + 1);
    EvenCaseTiredness(diff);
    assert result == tirednessForSteps(half) * 2;
    OptimalMeetingPointMinimizesTiredness(a, b);
  } else {
    var n1 := (diff + 1) / 2;
    var n2 := n1 - 1;
    result := n1 * n1;
    OddCaseSimplified(diff);
    assert result == tirednessForSteps(n1) + tirednessForSteps(n2);
    OptimalMeetingPointMinimizesTiredness(a, b);
  }
}
// </vc-code>

