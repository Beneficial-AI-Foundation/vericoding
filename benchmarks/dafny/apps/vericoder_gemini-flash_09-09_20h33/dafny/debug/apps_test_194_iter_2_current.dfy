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
function countDeniedPeopleIter(groups: seq<int>, a: int, b: int, halfOccupied: int, index: int): (denied: int)
    requires a >= 0 && b >= 0 && halfOccupied >= 0
    requires index <= |groups|
    requires forall i :: 0 <= i < |groups| ==> groups[i] == 1 || groups[i] == 2
    ensures denied >= 0
    decreases |groups| - index
{
    if index == |groups| then
        0
    else
        var group := groups[index];
        if group == 2 then
            if b > 0 then
                countDeniedPeopleIter(groups, a, b - 1, halfOccupied, index + 1)
            else
                2 + countDeniedPeopleIter(groups, a, b, halfOccupied, index + 1)
        else // group == 1
            if a > 0 then
                countDeniedPeopleIter(groups, a - 1, b, halfOccupied, index + 1)
            else if b > 0 then
                countDeniedPeopleIter(groups, a, b - 1, halfOccupied + 1, index + 1)
            else if halfOccupied > 0 then
                countDeniedPeopleIter(groups, a, b, halfOccupied - 1, index + 1)
            else
                1 + countDeniedPeopleIter(groups, a, b, halfOccupied, index + 1)
}

lemma countDeniedPeople_equals_Iter(groups: seq<int>, a: int, b: int, halfOccupied: int)
    requires a >= 0 && b >= 0 && halfOccupied >= 0
    requires forall i :: 0 <= i < |groups| ==> groups[i] == 1 || groups[i] == 2
    ensures countDeniedPeopleWithHalf(groups, a, b, halfOccupied) == countDeniedPeopleIter(groups, a, b, halfOccupied, 0)
    decreases |groups|
{
    if |groups| == 0 then
        // Base case: |groups| == 0
    else
        var group := groups[0];
        var rest := groups[1..];
        if group == 2 then
            if b > 0 then
                countDeniedPeople_equals_Iter(rest, a, b - 1, halfOccupied);
            else
                countDeniedPeople_equals_Iter(rest, a, b, halfOccupied);
        else // group == 1
            if a > 0 then
                countDeniedPeople_equals_Iter(rest, a - 1, b, halfOccupied);
            else if b > 0 then
                countDeniedPeople_equals_Iter(rest, a, b - 1, halfOccupied + 1);
            else if halfOccupied > 0 then
                countDeniedPeople_equals_Iter(rest, a, b, halfOccupied - 1);
            else
                countDeniedPeople_equals_Iter(rest, a, b, halfOccupied);
}

lemma countDeniedPeople_equals_Iter_main(groups: seq<int>, a: int, b: int)
    requires a >= 0 && b >= 0
    requires forall i :: 0 <= i < |groups| ==> groups[i] == 1 || groups[i] == 2
    ensures countDeniedPeople(groups, a, b) == countDeniedPeopleIter(groups, a, b, 0, 0)
{
    countDeniedPeople_equals_Iter(groups, a, b, 0);
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
    var currentA := a;
    var currentB := b;
    var currentHalfOccupied := 0;
    var deniedCount := 0;

    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant currentA >= 0 && currentB >= 0 && currentHalfOccupied >= 0
        invariant deniedCount == countDeniedPeopleIter(groups, a, b, 0, 0) - countDeniedPeopleIter(groups, currentA, currentB, currentHalfOccupied, i)
        // Alternative invariant for direct reasoning with the iterative function
        // invariant deniedCount == countDeniedPeopleIter(groups[0..i], a, b, 0, 0) - countDeniedPeopleIter(groups[0..i], currentA, currentB, currentHalfOccupied, i) // This would be for accumulated denied
        // A better invariant using the `countDeniedPeopleIter` helper:
        invariant deniedCount + countDeniedPeopleIter(groups, currentA, currentB, currentHalfOccupied, i) == countDeniedPeopleIter(groups, a, b, 0, 0)
        decreases n - i
    {
        var group := groups[i];
        if group == 2 then
            if currentB > 0 then
                currentB := currentB - 1;
            else
                deniedCount := deniedCount + 2;
        else // group == 1
            if currentA > 0 then
                currentA := currentA - 1;
            else if currentB > 0 then
                currentB := currentB - 1;
                currentHalfOccupied := currentHalfOccupied + 1;
            else if currentHalfOccupied > 0 then
                currentHalfOccupied := currentHalfOccupied - 1;
            else
                deniedCount := deniedCount + 1;
        i := i + 1;
    }
    countDeniedPeople_equals_Iter_main(groups, a, b); // Prove equivalence to countDeniedPeople
    denied := deniedCount;
}
// </vc-code>

