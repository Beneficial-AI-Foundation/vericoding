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
lemma countDeniedPeopleWithHalfLemma(groups: seq<int>, a: int, b: int, halfOccupied: int)
    requires a >= 0 && b >= 0 && halfOccupied >= 0
    requires forall i :: 0 <= i < |groups| ==> groups[i] == 1 || groups[i] == 2
    ensures countDeniedPeopleWithHalf(groups, a, b, halfOccupied) >= 0
    decreases |groups|
{
    if |groups| != 0 {
        var group := groups[0];
        var rest := groups[1..];
        if group == 2 {
            if b > 0 {
                countDeniedPeopleWithHalfLemma(rest, a, b - 1, halfOccupied);
            } else {
                countDeniedPeopleWithHalfLemma(rest, a, b, halfOccupied);
            }
        } else {
            if a > 0 {
                countDeniedPeopleWithHalfLemma(rest, a - 1, b, halfOccupied);
            } else if b > 0 {
                countDeniedPeopleWithHalfLemma(rest, a, b - 1, halfOccupied + 1);
            } else if halfOccupied > 0 {
                countDeniedPeopleWithHalfLemma(rest, a, b, halfOccupied - 1);
            } else {
                countDeniedPeopleWithHalfLemma(rest, a, b, halfOccupied);
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
    var remA := a;
    var remB := b;
    var halfCount := 0;
    denied := 0;
    var idx := 0;
    
    while idx < |groups|
        invariant 0 <= idx <= |groups|
        invariant remA >= 0 && remB >= 0 && halfCount >= 0
        invariant denied + countDeniedPeopleWithHalf(groups[idx..], remA, remB, halfCount) == countDeniedPeopleWithHalf(groups, a, b, 0)
    {
        var group := groups[idx];
        idx := idx + 1;
        
        if group == 2 {
            if remB > 0 {
                remB := remB - 1;
            } else {
                denied := denied + 2;
            }
        } else { // group == 1
            if remA > 0 {
                remA := remA - 1;
            } else if remB > 0 {
                remB := remB - 1;
                halfCount := halfCount + 1;
            } else if halfCount > 0 {
                halfCount := halfCount - 1;
            } else {
                denied := denied + 1;
            }
        }
    }
    
    countDeniedPeopleWithHalfLemma(groups, a, b, 0);
}
// </vc-code>

