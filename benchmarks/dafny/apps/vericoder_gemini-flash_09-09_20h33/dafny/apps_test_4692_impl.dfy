predicate ValidInput(M: int)
{
    1 <= M <= 23
}

function HoursUntilNewYear(M: int): int
    requires ValidInput(M)
{
    48 - M
}

predicate ValidOutput(M: int, result: int)
    requires ValidInput(M)
{
    result == HoursUntilNewYear(M) && 25 <= result <= 47
}

// <vc-helpers>
lemma lemma_HoursUntilNewYear_bounds(M: int)
    requires ValidInput(M)
    ensures 25 <= HoursUntilNewYear(M) <= 47
{
    // ValidInput(M) implies 1 <= M <= 23
    // HoursUntilNewYear(M) is 48 - M

    // Lower bound for HoursUntilNewYear(M):
    // Since M <= 23,
    // -M >= -23
    // 48 - M >= 48 - 23
    // 48 - M >= 25
    calc {
        48 - M;
        >= 48 - 23;  // because M <= 23
        25;
    }

    // Upper bound for HoursUntilNewYear(M):
    // Since M >= 1,
    // -M <= -1
    // 48 - M <= 48 - 1
    // 48 - M <= 47
    calc {
        48 - M;
        <= 48 - 1;   // because M >= 1
        47;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(M: int) returns (result: int)
    requires ValidInput(M)
    ensures ValidOutput(M, result)
// </vc-spec>
// <vc-code>
{
    result := 48 - M;
    lemma_HoursUntilNewYear_bounds(M); // Prove that the result is within the required range
}
// </vc-code>

