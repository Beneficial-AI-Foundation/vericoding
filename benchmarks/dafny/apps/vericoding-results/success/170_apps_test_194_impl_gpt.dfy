predicate ValidInput(n: int, a: int, b: int, groups: seq<int>)
{
    n >= 1 && a >= 1 && b >= 1 && |groups| == n &&
    forall i :: 0 <= i < |groups| ==> groups[i] == 1 || groups[i] == 2
}

function countDeniedPeople(groups: seq<int>, a: int, b: int): int
    requires a >= 0 && b >= 0
    requires forall i :: 0 <= i < |groups| ==> groups[i] == 1 || groups[i] == 2
    decreases |groups|
{
    countDeniedPeopleWithHalf(groups, a, b, 0)
}

function countDeniedPeopleWithHalf(groups: seq<int>, a: int, b: int, halfOccupied: int): int
    requires a >= 0 && b >= 0 && halfOccupied >= 0
    requires forall i :: 0 <= i < |groups| ==> groups[i] == 1 || groups[i] == 2
    decreases |groups|
{
    if |groups| == 0 then 0
    else
        var group := groups[0];
        var rest := groups[1..];
        if group == 2 then
            if b > 0 then countDeniedPeopleWithHalf(rest, a, b - 1, halfOccupied)
            else 2 + countDeniedPeopleWithHalf(rest, a, b, halfOccupied)
        else // group == 1
            if a > 0 then countDeniedPeopleWithHalf(rest, a - 1, b, halfOccupied)
            else if b > 0 then countDeniedPeopleWithHalf(rest, a, b - 1, halfOccupied + 1)
            else if halfOccupied > 0 then countDeniedPeopleWithHalf(rest, a, b, halfOccupied - 1)
            else 1 + countDeniedPeopleWithHalf(rest, a, b, halfOccupied)
}

// <vc-helpers>
lemma TailPreservesGroupElems(groups: seq<int>)
    requires |groups| > 0
    requires forall i :: 0 <= i < |groups| ==> groups[i] == 1 || groups[i] == 2
    ensures forall i :: 0 <= i < |groups[1..]| ==> groups[1..][i] == 1 || groups[1..][i] == 2
{
  assert |groups[1..]| == |groups| - 1;
  forall i | 0 <= i < |groups[1..]|
    ensures groups[1..][i] == 1 || groups[1..][i] == 2
  {
    assert 0 <= i + 1;
    assert i + 1 < |groups|;
    assert groups[i + 1] == 1 || groups[i + 1] == 2;
    assert groups[1..][i] == groups[i + 1];
  }
}

lemma CountDeniedWithHalfNonNegative(groups: seq<int>, a: int, b: int, halfOccupied: int)
    requires a >= 0 && b >= 0 && halfOccupied >= 0
    requires forall i :: 0 <= i < |groups| ==> groups[i] == 1 || groups[i] == 2
    ensures countDeniedPeopleWithHalf(groups, a, b, halfOccupied) >= 0
    decreases |groups|
{
  if |groups| == 0 {
    assert countDeniedPeopleWithHalf(groups, a, b, halfOccupied) == 0;
  } else {
    assert groups[0] == 1 || groups[0] == 2;
    TailPreservesGroupElems(groups);
    var rest := groups[1..];
    if groups[0] == 2 {
      if b > 0 {
        assert countDeniedPeopleWithHalf(groups, a, b, halfOccupied) ==
               countDeniedPeopleWithHalf(rest, a, b - 1, halfOccupied);
        CountDeniedWithHalfNonNegative(rest, a, b - 1, halfOccupied);
      } else {
        CountDeniedWithHalfNonNegative(rest, a, b, halfOccupied);
        assert countDeniedPeopleWithHalf(groups, a, b, halfOccupied) ==
               2 + countDeniedPeopleWithHalf(rest, a, b, halfOccupied);
        assert 2 + countDeniedPeopleWithHalf(rest, a, b, halfOccupied) >= 0;
      }
    } else {
      if a > 0 {
        assert countDeniedPeopleWithHalf(groups, a, b, halfOccupied) ==
               countDeniedPeopleWithHalf(rest, a - 1, b, halfOccupied);
        CountDeniedWithHalfNonNegative(rest, a - 1, b, halfOccupied);
      } else if b > 0 {
        assert countDeniedPeopleWithHalf(groups, a, b, halfOccupied) ==
               countDeniedPeopleWithHalf(rest, a, b - 1, halfOccupied + 1);
        CountDeniedWithHalfNonNegative(rest, a, b - 1, halfOccupied + 1);
      } else if halfOccupied > 0 {
        assert countDeniedPeopleWithHalf(groups, a, b, halfOccupied) ==
               countDeniedPeopleWithHalf(rest, a, b, halfOccupied - 1);
        CountDeniedWithHalfNonNegative(rest, a, b, halfOccupied - 1);
      } else {
        CountDeniedWithHalfNonNegative(rest, a, b, halfOccupied);
        assert countDeniedPeopleWithHalf(groups, a, b, halfOccupied) ==
               1 + countDeniedPeopleWithHalf(rest, a, b, halfOccupied);
        assert 1 + countDeniedPeopleWithHalf(rest, a, b, halfOccupied) >= 0;
      }
    }
  }
}

lemma CountDeniedNonNegative(groups: seq<int>, a: int, b: int)
    requires a >= 0 && b >= 0
    requires forall i :: 0 <= i < |groups| ==> groups[i] == 1 || groups[i] == 2
    ensures countDeniedPeople(groups, a, b) >= 0
{
  assert countDeniedPeople(groups, a, b) == countDeniedPeopleWithHalf(groups, a, b, 0);
  CountDeniedWithHalfNonNegative(groups, a, b, 0);
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int, groups: seq<int>) returns (denied: int)
    requires ValidInput(n, a, b, groups)
    ensures denied >= 0
    ensures denied == countDeniedPeople(groups, a, b)
// </vc-spec>
// <vc-code>
{
  denied := countDeniedPeople(groups, a, b);
  CountDeniedNonNegative(groups, a, b);
}
// </vc-code>

