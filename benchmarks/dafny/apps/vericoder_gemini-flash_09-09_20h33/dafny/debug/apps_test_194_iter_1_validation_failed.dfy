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
    var totalDenied := 0;

    for i := 0 to n - 1
        invariant 0 <= i <= n
        invariant currentA >= 0 && currentB >= 0 && currentHalfOccupied >= 0
        invariant totalDenied == countDeniedPeopleWithHalf(groups[0..i], a, b, 0) - countDeniedPeopleWithHalf(groups[0..i], currentA, currentB, currentHalfOccupied)
        invariant totalDenied == countDeniedPeopleWithHalf(groups[0..i], a, b, 0) - countDeniedPeople(groups[i..], currentA, currentB) + countDeniedPeople(groups[i..], currentA, currentB) - countDeniedPeopleWithHalf(groups[i..], currentA, currentB, currentHalfOccupied)
        invariant totalDenied == countDeniedPeople(groups[0..i], a, b) - countDeniedPeople(groups[i..], currentA, currentB)
        // More precise invariant for totalDenied, relating to actual function definition
        // This relies on the structure of the countDeniedPeople functions.
        // It's essentially totalDenied = (initial groups taken) - (remaining groups with updated capacity)
        // However, a simpler loop invariant that accumulates denied people directly might be easier to prove.
        // Let's re-evaluate totalDenied.

        // Loop Invariant for totalDenied:
        // totalDenied represents the number of people denied access so far, assuming the capacities
        // 'a', 'b', and 'halfOccupied' were initially 'a', 'b', and '0' respectively for the *entire* initial 'groups' seq.
        // After processing 'groups[0..i-1]', 'currentA', 'currentB', and 'currentHalfOccupied' reflect the
        // remaining capacities *if* we started with 'a', 'b', '0' for the sequence 'groups[i..n-1]'.
        // So, totalDenied is the count of denied people for groups[0..i-1] *given initial a,b,0*
        // PLUS the difference in denied count from original (a,b,0) to remaining (currentA, currentB, currentHalfOccupied)
        // for the first 'i' processed groups.

        // A simpler, standard approach:
        // totalDenied is the count of denied people up to index i-1.
        // currentA, currentB, currentHalfOccupied are the remaining capacities after processing groups[0..i-1].
        // So, the total number of denied people, if we were to compute it from scratch with (a,b,0),
        // should be totalDenied + countDeniedPeopleWithHalf(groups[i..], currentA, currentB, currentHalfOccupied).
        // This is the strongest postcondition for the loop body.

        // The exact invariant for 'totalDenied' is trickier due to the recursive definition.
        // Let's try to make `denied` accumulate the *exact* number of denied people from the start.
        // And `currentA`, `currentB`, `currentHalfOccupied` truly reflect the remaining capacities.

        // Define a function for the state of the system at index i:
        // state(i, initial_a, initial_b, initial_half_occupied) =
        //    (denied_so_far, remaining_a, remaining_b, remaining_half_occupied)
        // The loop is essentially computing this iteratively.

        // Try a more direct invariant from method `solve`'s ensures clause:
        // The desired final state is `denied == countDeniedPeople(groups, a, b)`.
        // This can be expressed as:
        // `denied` tracks the sum of people denied.
        // `currentA`, `currentB`, `currentHalfOccupied` track the current capacities.
        //
        // Invariant:
        // `totalDenied + countDeniedPeopleWithHalf(groups[i..], currentA, currentB, currentHalfOccupied) == countDeniedPeople(groups, a, b)`
        // This is a common invariant structure for these kinds of problems (sum of parts).
        // Let's prove it for the loop:

        // Base case (i=0):
        // totalDenied = 0
        // currentA = a
        // currentB = b
        // currentHalfOccupied = 0
        // 0 + countDeniedPeopleWithHalf(groups[0..n], a, b, 0) == countDeniedPeople(groups, a, b)
        // This holds by definition of countDeniedPeople.

        // Inductive step: Assume it holds for `i`, prove for `i+1`.
        // Let `i` be the start of the loop iteration.
        // We know: `totalDenied_i + countDeniedPeopleWithHalf(groups[i..], currentA_i, currentB_i, currentHalfOccupied_i) == countDeniedPeople(groups, a, b)`

        // Inside the loop:
        var group := groups[i];
        var nextHalfOccupied := currentHalfOccupied;
        var nextA := currentA;
        var nextB := currentB;
        var deniedInThisStep := 0;

        if group == 2 {
            if nextB > 0 {
                nextB := nextB - 1;
            } else {
                deniedInThisStep := 2;
            }
        } else { // group == 1
            if nextA > 0 {
                nextA := nextA - 1;
            } else if nextB > 0 {
                nextB := nextB - 1;
                nextHalfOccupied := nextHalfOccupied + 1;
            } else if nextHalfOccupied > 0 {
                nextHalfOccupied := nextHalfOccupied - 1;
            } else {
                deniedInThisStep := 1;
            }
        }
        // Update loop variables:
        // totalDenied := totalDenied + deniedInThisStep;
        // currentA := nextA;
        // currentB := nextB;
        // currentHalfOccupied := nextHalfOccupied;

        // Now, we need to show:
        // `(totalDenied_i + deniedInThisStep) + countDeniedPeopleWithHalf(groups[i+1..], nextA, nextB, nextHalfOccupied) == countDeniedPeople(groups, a, b)`

        // From the definition of countDeniedPeopleWithHalf:
        // `countDeniedPeopleWithHalf(groups[i..], currentA_i, currentB_i, currentHalfOccupied_i)`
        // `==`  (if groups[i] == 2)
        //   `if currentB_i > 0 then countDeniedPeopleWithHalf(groups[i+1..], currentA_i, currentB_i - 1, currentHalfOccupied_i) `
        //   `else 2 + countDeniedPeopleWithHalf(groups[i+1..], currentA_i, currentB_i, currentHalfOccupied_i)`
        // `== ` (substituting `nextA`, `nextB`, `nextHalfOccupied`, `deniedInThisStep`)
        //   `deniedInThisStep + countDeniedPeopleWithHalf(groups[i+1..], nextA, nextB, nextHalfOccupied)`

        // So, `countDeniedPeopleWithHalf(groups[i..], currentA_i, currentB_i, currentHalfOccupied_i)`
        //    `= deniedInThisStep + countDeniedPeopleWithHalf(groups[i+1..], nextA, nextB, nextHalfOccupied)`

        // Substitute this back into the inductive hypothesis:
        // `totalDenied_i + (deniedInThisStep + countDeniedPeopleWithHalf(groups[i+1..], nextA, nextB, nextHalfOccupied)) == countDeniedPeople(groups, a, b)`
        // `(totalDenied_i + deniedInThisStep) + countDeniedPeopleWithHalf(groups[i+1..], nextA, nextB, nextHalfOccupied) == countDeniedPeople(groups, a, b)`
        // This is exactly what we need for the next iteration (i+1).

        // Acknowledging the complexity, Dafny might need some help with the invariant.
        // Let's add the values directly.
    {
        var group := groups[i];
        if group == 2 {
            if currentB > 0 {
                currentB := currentB - 1;
            } else {
                totalDenied := totalDenied + 2;
            }
        } else { // group == 1
            if currentA > 0 {
                currentA := currentA - 1;
            } else if currentB > 0 {
                currentB := currentB - 1;
                currentHalfOccupied := currentHalfOccupied + 1;
            } else if currentHalfOccupied > 0 {
                currentHalfOccupied := currentHalfOccupied - 1;
            } else {
                totalDenied := totalDenied + 1;
            }
        }
    }

    denied := totalDenied;
    return denied;
}
// </vc-code>

