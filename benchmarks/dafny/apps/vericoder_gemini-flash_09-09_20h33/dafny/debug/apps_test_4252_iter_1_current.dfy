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

// <vc-helpers>
function ConsecutiveXCountFromEnd(s: string, pos: int): int
    requires 0 <= pos <= |s|
    ensures ConsecutiveXCountFromEnd(s, pos) >= 0
    ensures ConsecutiveXCountFromEnd(s, pos) <= pos
{
    if pos == 0 then 0
    else if s[pos - 1] == 'x' then 1 + ConsecutiveXCountFromEnd(s, pos - 1)
    else 0
}

lemma CountExcessivePositionsHelperLemma(s: string, pos: int, consecutiveX: int)
    requires 0 <= pos <= |s|
    requires consecutiveX >= 0
    ensures CountExcessivePositionsHelper(s, pos, consecutiveX) == CountExcessivePositionsFunction(s, pos, consecutiveX)
{
    if pos >= |s| {
        // Base case, both return 0
    } else {
        var newConsecutiveX := if s[pos] == 'x' then consecutiveX + 1 else 0;
        var currentContribution := if newConsecutiveX > 2 then 1 else 0;
        
        // Recursive call lemma application
        CountExcessivePositionsHelperLemma(s, pos + 1, newConsecutiveX);
    }
}

function CountExcessivePositionsFunction(s: string, pos: int, consecutiveX: int): int
    requires 0 <= pos <= |s|
    requires consecutiveX >= 0
{
    if pos >= |s| then 0
    else
        var newConsecutiveX := if s[pos] == 'x' then consecutiveX + 1 else 0;
        var currentContribution := if newConsecutiveX > 2 then 1 else 0;
        currentContribution + CountExcessivePositionsFunction(s, pos + 1, newConsecutiveX)
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures result >= 0
    ensures result <= |s|
    ensures result == CountExcessivePositions(s)
// </vc-spec>
// <vc-code>
{
    var result := 0;
    var consecutiveX := 0;
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant consecutiveX >= 0
        invariant result >= 0
        invariant result == CountExcessivePositionsHelper(s, 0, 0) - CountExcessivePositionsHelper(s, i, consecutiveX)
        // More precise: result == (sum of contributions from 0 to i-1)
        // Let's refine the invariant to directly relate to the target
        invariant result == CountExcessivePositionsFunction(s, 0, 0) - CountExcessivePositionsFunction(s, i, consecutiveX)
    {
        if i < |s| {
            var newConsecutiveX := if s[i] == 'x' then consecutiveX + 1 else 0;
            var currentContribution := if newConsecutiveX > 2 then 1 else 0;
            result := result + currentContribution;
            consecutiveX := newConsecutiveX;
        }
    }
    // After the loop, i == |s|
    // Our invariant directly implies:
    // result == CountExcessivePositionsFunction(s, 0, 0) - CountExcessivePositionsFunction(s, |s|, consecutiveX)
    // Since CountExcessivePositionsFunction(s, |s|, consecutiveX) is 0,
    // result == CountExcessivePositionsFunction(s, 0, 0)
    // Applying CountExcessivePositionsHelperLemma(s, 0, 0):
    // result == CountExcessivePositionsHelper(s, 0, 0)
    // And by definition of CountExcessivePositions, result == CountExcessivePositions(s)
    
    return result;
}
// </vc-code>

