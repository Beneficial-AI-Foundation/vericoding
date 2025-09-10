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
lemma countDeniedPeopleEquivalence(groups: seq<int>, a: int, b: int)
    requires a >= 0 && b >= 0
    requires forall i :: 0 <= i < |groups| ==> groups[i] == 1 || groups[i] == 2
    ensures countDeniedPeople(groups, a, b) == countDeniedPeopleWithHalf(groups, a, b, 0)
{
    // This follows directly from the definition
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
    var availableA := a;
    var availableB := b;
    var halfOccupied := 0;
    denied := 0;
    
    var i := 0;
    
    while i < |groups|
        invariant 0 <= i <= |groups|
        invariant availableA >= 0 && availableB >= 0 && halfOccupied >= 0
        invariant denied >= 0
        invariant denied + countDeniedPeopleWithHalf(groups[i..], availableA, availableB, halfOccupied) == 
                  countDeniedPeopleWithHalf(groups, a, b, 0)
    {
        var group := groups[i];
        
        if group == 2 {
            if availableB > 0 {
                availableB := availableB - 1;
            } else {
                denied := denied + 2;
            }
        } else { // group == 1
            if availableA > 0 {
                availableA := availableA - 1;
            } else if availableB > 0 {
                availableB := availableB - 1;
                halfOccupied := halfOccupied + 1;
            } else if halfOccupied > 0 {
                halfOccupied := halfOccupied - 1;
            } else {
                denied := denied + 1;
            }
        }
        
        i := i + 1;
    }
    
    assert groups[i..] == [];
    assert countDeniedPeopleWithHalf([], availableA, availableB, halfOccupied) == 0;
}
// </vc-code>

