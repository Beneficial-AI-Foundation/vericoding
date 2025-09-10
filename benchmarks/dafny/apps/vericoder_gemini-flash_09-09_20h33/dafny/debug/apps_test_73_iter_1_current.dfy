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
function method computePositionInvariant(days: int, v0: int, v1: int, a: int, l: int, c: int): bool
    requires days >= 0
    requires v0 >= 0 && v1 >= v0 && a >= 0 && l >= 0
    reads this
{
    computePosition(days, v0, v1, a, l) < c
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
    var high := c; // Upper bound, as in the worst case, we might read 1 unit per day.

    var result_candidate := high; // Initialize with a value that satisfies the upper bound

    while low <= high
        invariant 1 <= low <= high + 1
        invariant forall days :: 1 <= days < low ==> computePosition(days, v0, v1, a, l) < c
        invariant computePosition(result_candidate, v0, v1, a, l) >= c
        invariant result_candidate >= low
    {
        var mid := low + (high - low) / 2;
        if computePosition(mid, v0, v1, a, l) >= c then
            result_candidate := mid;
            high := mid - 1;
        else
            low := mid + 1;
        
        // This assertion is to help Dafny with the invariant.
        // It asserts that if computePosition(mid, ...) < c, then for
        // the next iteration, all days < low (which is mid+1) also have
        // computePosition(...) < c.
        // If computePosition(mid, ...) >= c, then result_candidate is updated to mid,
        // and high becomes mid-1. The invariant `forall days :: 1 <= days < low ==> computePosition(days, v0, v1, a, l) < c` holds.
        // The other invariant `computePosition(result_candidate, v0, v1, a, l) >= c` holds by assignment.
        // `result_candidate >= low` holds in both branches.
    }
    return result_candidate;
}
// </vc-code>

