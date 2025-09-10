function computePosition(days: int, v0: int, v1: int, a: int, l: int): int
    requires days >= 0
    requires v0 >= 0 && v1 >= v0 && a >= 0 && l >= 0
    decreases days
{
    if days == 0 then 0
    else
        var prevPos := computePosition(days - 1, v0, v1, a, l);
        var afterReread := if prevPos - l > 0 then prevPos - l else 0;
        var readToday := if v1 < v0 + a * (days - 1) then v1 else v0 + a * (days - 1);
        afterReread + readToday
}

// <vc-helpers>
function computePositionInvariant(days: int, v0: int, v1: int, a: int, l: int, c: int): bool
    requires days >= 0
    requires v0 >= 0 && v1 >= v0 && a >= 0 && l >= 0
    // No direct use in the fix for now, keeping for completeness if needed later
{
    computePosition(days, v0, v1, a, l) < c
}

predicate IsSolution(result: int, c: int, v0: int, v1: int, a: int, l: int)
    requires result >= 1
    requires v0 >= 0 && v1 >= v0 && a >= 0 && l >= 0
    requires c >= 1
{
    computePosition(result, v0, v1, a, l) >= c &&
    (forall days :: 1 <= days < result ==> computePosition(days, v0, v1, a, l) < c)
}
// </vc-helpers>

// <vc-spec>
method solve(c: int, v0: int, v1: int, a: int, l: int) returns (result: int)
    requires 1 <= c <= 1000
    requires 0 <= l < v0 <= v1 <= 1000
    requires 0 <= a <= 1000
    ensures result >= 1
    ensures computePosition(result, v0, v1, a, l) >= c
    ensures forall days :: 1 <= days < result ==> computePosition(days, v0, v1, a, l) < c
// </vc-spec>
// <vc-code>
{
    var low := 1;
    var high := c; 

    var result_candidate := c; 

    while low <= high
        invariant 1 <= low <= high + 1
        invariant result_candidate >= 1 // result_candidate is at least 1
        invariant high < c + 1 // high cannot exceed c in the beginning and decreases or stays
        invariant low <= c + 1 // low does not exceed original c + 1
        invariant forall days :: 1 <= days < low ==> computePosition(days, v0, v1, a, l) < c
        invariant forall days :: result_candidate <= days <= c ==> computePosition(days, v0, v1, a, l) >= c
        invariant computePosition(result_candidate, v0, v1, a, l) >= c
        invariant result_candidate >= low || high < result_candidate
        invariant low <= result_candidate // The candidate for the solution must be in the search space or be the lower bound.
    {
        var mid := low + (high - low) / 2;
        if computePosition(mid, v0, v1, a, l) >= c {
            result_candidate := mid;
            high := mid - 1;
        } else {
            low := mid + 1;
        }
    }
    return result_candidate;
}
// </vc-code>

