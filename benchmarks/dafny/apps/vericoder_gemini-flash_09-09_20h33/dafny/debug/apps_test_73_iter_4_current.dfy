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
{
    computePosition(days, v0, v1, a, l) < c
}

predicate IsSolution(result: int, c: int, v0: int, v1: int, a: int, l: int)
    requires result >= 1
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
    var high := c; // Upper bound, as in the worst case, we might read 1 unit per day.

    var result_candidate := c; // Initialize with a value that satisfies the upper bound

    while low <= high
        invariant 1 <= low <= high + 1 <= c + 1
        invariant 1 <= result_candidate <= c
        invariant IsSolution(result_candidate, c, v0, v1, a, l) ==> result_candidate <= high + 1
        invariant low <= result_candidate
        invariant forall days :: 1 <= days < low ==> computePosition(days, v0, v1, a, l) < c
        invariant forall days :: high < days <= c ==> computePosition(days, v0, v1, a, l) >= c
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

