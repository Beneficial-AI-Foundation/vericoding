predicate ValidInput(a: int, b: int, c: int, d: int)
{
    a >= 0 && b >= 0 && c >= 0 && d >= 0
}

predicate FirstAlarmSufficient(a: int, b: int)
{
    a <= b
}

predicate NeverWakes(a: int, b: int, c: int, d: int)
{
    a > b && c <= d
}

predicate EventuallyWakes(a: int, b: int, c: int, d: int)
{
    a > b && c > d
}

function CalculateWakeTime(a: int, b: int, c: int, d: int): int
    requires ValidInput(a, b, c, d)
    requires EventuallyWakes(a, b, c, d)
{
    var remaining := a - b;
    var cycles := (remaining - 1) / (c - d) + 1;
    b + c * cycles
}

// <vc-helpers>
lemma Lemma_EventuallyWakes_PositiveCycles(a: int, b: int, c: int, d: int)
    requires EventuallyWakes(a, b, c, d)
    ensures (a - b - 1) / (c - d) + 1 >= 1
{
    var num := a - b - 1;
    var den := c - d;

    assert a - b >= 1; // Since a > b and a, b are integers
    assert c - d >= 1; // Since c > d and c, d are integers

    // Case 1: num >= 0
    if num >= 0 {
        assert num / den >= 0;
        assert (num / den) + 1 >= 1;
    } else { // Case 2: num < 0. This implies a - b - 1 < 0, so a - b = 0. But a > b, so a - b >= 1. Contradiction.
             // Therefore, num must be non-negative given the precondition a > b.
        // Actually, num can be -1 if a-b is 0, which is not possible
        // If a-b = 1, then num = 0
        // If a-b = 2, then num = 1
        // (a-b-1) and (c-d) are guaranteed to be non-negative based on EventuallyWakes.
    }
}

lemma Lemma_EventuallyWakes_RemainingNonNegative(a: int, b: int, c: int, d: int)
    requires EventuallyWakes(a, b, c, d)
    ensures a - b >= 0
{
    // Follows directly from a > b
}

lemma Lemma_EventuallyWakes_CDNonNegative(a: int, b: int, c: int, d: int)
    requires EventuallyWakes(a, b, c, d)
    ensures c - d >= 0
{
    // Follows directly from c > d
}

lemma Lemma_EventuallyWakes_RemainingMinusOne(a: int, b: int, c: int, d: int)
    requires EventuallyWakes(a, b, c, d)
    ensures (a - b - 1) < (a - b)
{
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, c: int, d: int) returns (result: int)
    requires ValidInput(a, b, c, d)
    ensures FirstAlarmSufficient(a, b) ==> result == b
    ensures NeverWakes(a, b, c, d) ==> result == -1
    ensures EventuallyWakes(a, b, c, d) ==> result == CalculateWakeTime(a, b, c, d)
// </vc-spec>
// <vc-code>
{
    if FirstAlarmSufficient(a, b) {
        return b;
    } else if NeverWakes(a, b, c, d) {
        return -1;
    } else {
        // Must be EventuallyWakes(a, b, c, d)
        // Prove this by showing that the conditions are exhaustive
        // We know a > b from the else branches.
        // If c <= d, it would be NeverWakes. Since it's not NeverWakes, c must be > d.
        // Thus, EventuallyWakes(a, b, c, d) holds.

        // Need to ensure the conditions for CalculateWakeTime are met
        // ValidInput(a, b, c, d) is a precondition of solve method.
        // EventuallyWakes(a, b, c, d) is shown above.
        Lemma_EventuallyWakes_PositiveCycles(a, b, c, d);
        Lemma_EventuallyWakes_RemainingNonNegative(a, b, c, d);
        Lemma_EventuallyWakes_CDNonNegative(a, b, c, d);
        Lemma_EventuallyWakes_RemainingMinusOne(a, b, c, d);

        var remaining := a - b;
        var cycles := (remaining - 1) / (c - d) + 1;
        return b + c * cycles;
    }
}
// </vc-code>

