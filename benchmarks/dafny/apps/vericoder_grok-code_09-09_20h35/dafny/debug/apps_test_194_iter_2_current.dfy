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
lemma CountNonNegative(groups: seq<int>, a: int, b: int, half: int)
    requires a >= 0 && b >= 0 && half >= 0
    requires forall i :: 0 <= i < |groups| ==> groups[i] == 1 || groups[i] == 2
    ensures countDeniedPeopleWithHalf(groups, a, b, half) >= 0
{
    var result := countDeniedPeopleWithHalf(groups, a, b, half);
    if |groups| == 0 {
        assert result == 0;
    } else {
        var group := groups[0];
        var rest := groups[1..];
        if group == 2 {
            if b > 0 {
                CountNonNegative(rest, a, b - 1, half);
                calc {
                    result;
                    == countDeniedPeopleWithHalf(rest, a, b - 1, half);
                }
            } else {
                CountNonNegative(rest, a, b, half);
                calc {
                    result;
                    == 2 + countDeniedPeopleWithHalf(rest, a, b, half);
                }
            }
        } else {
            if a > 0 {
                CountNonNegative(rest, a - 1, b, half);
                calc {
                    result;
                    == countDeniedPeopleWithHalf(rest, a - 1, b, half);
                }
            } else if b > 0 {
                CountNonNegative(rest, a, b - 1, half + 1);
                calc {
                    result;
                    == countDeniedPeopleWithHalf(rest, a, b - 1, half + 1);
                }
            } else if half > 0 {
                CountNonNegative(rest, a, b, half - 1);
                calc {
                    result;
                    == countDeniedPeopleWithHalf(rest, a, b, half - 1);
                }
            } else {
                CountNonNegative(rest, a, b, half);
                calc {
                    result;
                    == 1 + countDeniedPeopleWithHalf(rest, a, b, half);
                }
            }
        }
    }
    assert result >= 0;
}

lemma CountDeniedNonNegative(groups: seq<int>, a: int, b: int)
    requires a >= 0 && b >= 0
    requires forall i :: 0 <= i < |groups| ==> groups[i] == 1 || groups[i] == 2
    ensures countDeniedPeople(groups, a, b) >= 0
{
    CountNonNegative(groups, a, b, 0);
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
    CountDeniedNonNegative(groups, a, b);
    denied := countDeniedPeople(groups, a, b);
}
// </vc-code>

