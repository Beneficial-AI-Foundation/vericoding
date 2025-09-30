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
lemma HoursUntilNewYearBounds(M: int)
    requires ValidInput(M)
    ensures 25 <= HoursUntilNewYear(M) <= 47
{
    // M is between 1 and 23
    // So 48 - M is between 48 - 23 = 25 and 48 - 1 = 47
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
    HoursUntilNewYearBounds(M);
}
// </vc-code>

