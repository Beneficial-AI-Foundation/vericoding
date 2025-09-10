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
lemma CountDeniedPeopleWithHalfNonNeg(groups: seq<int>, a: int, b: int, halfOccupied: int)
    requires a >= 0 && b >= 0 && halfOccupied >= 0
    requires forall i :: 0 <= i < |groups| ==> groups[i] == 1 || groups[i] == 2
    ensures countDeniedPeopleWithHalf(groups, a, b, halfOccupied) >= 0
    decreases |groups|
{
    if |groups| == 0 {
        // base case: function returns 0
    } else {
        var group := groups[0];
        var rest := groups[1..];
        if group == 2 {
            if b > 0 {
                CountDeniedPeopleWithHalfNonNeg(rest, a, b - 1, halfOccupied);
            } else {
                // countDeniedPeopleWithHalf(groups,a,b,halfOccupied) == 2 + countDeniedPeopleWithHalf(rest,a,b,halfOccupied)
                CountDeniedPeopleWithHalfNonNeg(rest, a, b, halfOccupied);
            }
        } else { // group == 1
            if a > 0 {
                CountDeniedPeopleWithHalfNonNeg(rest, a - 1, b, halfOccupied);
            } else if b > 0 {
                CountDeniedPeopleWithHalfNonNeg(rest, a, b - 1, halfOccupied + 1);
            } else if halfOccupied > 0 {
                CountDeniedPeopleWithHalfNonNeg(rest, a, b, halfOccupied - 1);
            } else {
                // countDeniedPeopleWithHalf(groups,a,b,halfOccupied) == 1 + countDeniedPeopleWithHalf(rest,a,b,halfOccupied)
                CountDeniedPeopleWithHalfNonNeg(rest, a, b, halfOccupied);
            }
        }
    }
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
  CountDeniedPeopleWithHalfNonNeg(groups, a, b, 0);
  denied := countDeniedPeople(groups, a, b);
}
// </vc-code>

