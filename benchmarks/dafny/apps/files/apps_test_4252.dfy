Given a string of lowercase Latin letters, find the minimum number of characters 
to remove so that the resulting string does not contain "xxx" (three consecutive x's) 
as a substring. Characters can be removed from any positions. If the string initially 
doesn't contain "xxx", return 0.

predicate ValidInput(s: string) 
{
    |s| >= 3
}

function CountExcessivePositions(s: string): int
{
    CountExcessivePositionsHelper(s, 0, 0)
}

function CountExcessivePositionsHelper(s: string, pos: int, consecutiveX: int): int
    requires 0 <= pos <= |s|
    requires consecutiveX >= 0
    decreases |s| - pos
{
    if pos >= |s| then 0
    else
        var newConsecutiveX := if s[pos] == 'x' then consecutiveX + 1 else 0;
        var currentContribution := if newConsecutiveX > 2 then 1 else 0;
        currentContribution + CountExcessivePositionsHelper(s, pos + 1, newConsecutiveX)
}

function ConsecutiveXCount(s: string, pos: int): int
    requires 0 <= pos <= |s|
{
    if pos == 0 then 0
    else if s[pos - 1] == 'x' then 1 + ConsecutiveXCount(s, pos - 1)
    else 0
}

method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures result >= 0
    ensures result <= |s|
    ensures result == CountExcessivePositions(s)
{
    result := 0;
    var x_count := 0;

    for i := 0 to |s|
        invariant 0 <= result <= i
        invariant x_count >= 0
        invariant result == CountExcessivePositionsHelper(s, 0, 0) - CountExcessivePositionsHelper(s, i, x_count)
        invariant x_count == ConsecutiveXCount(s, i)
    {
        if s[i] == 'x' {
            x_count := x_count + 1;
        } else {
            x_count := 0;
        }

        if x_count > 2 {
            result := result + 1;
        }
    }
}
