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
lemma SubsequencePropertyHelper(s: seq<int>, i: int)
    requires 0 <= i <= |s|
    requires forall k :: 0 <= k < |s| ==> s[k] == 1 || s[k] == 2
    ensures forall k :: 0 <= k < |s[i..]| ==> s[i..][k] == 1 || s[i..][k] == 2
{
    
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
    var current_a := a;
    var current_b := b;
    var half_occupied := 0;
    denied := 0;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant current_a >= 0 && current_b >= 0 && half_occupied >= 0
        invariant denied + countDeniedPeopleWithHalf(groups[i..], current_a, current_b, half_occupied) == countDeniedPeople(groups, a, b)
        decreases n - i
    {
        SubsequencePropertyHelper(groups, i);
        var group := groups[i];
        if group == 2 {
            if current_b > 0 {
                current_b := current_b - 1;
            } else {
                denied := denied + 2;
            }
        } else { // group == 1
            if current_a > 0 {
                current_a := current_a - 1;
            } else if current_b > 0 {
                current_b := current_b - 1;
                half_occupied := half_occupied + 1;
            } else if half_occupied > 0 {
                half_occupied := half_occupied - 1;
            } else {
                denied := denied + 1;
            }
        }
        i := i + 1;
    }
}
// </vc-code>

