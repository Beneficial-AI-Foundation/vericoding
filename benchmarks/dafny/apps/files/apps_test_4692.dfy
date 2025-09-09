Calculate how many hours remain from M o'clock (24-hour format) on December 30th 
until New Year (0 o'clock on January 1st). M is an integer between 1 and 23 inclusive.

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

method solve(M: int) returns (result: int)
    requires ValidInput(M)
    ensures ValidOutput(M, result)
{
    result := 48 - M;
}
