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
    decreases |s| - pos
{
    if pos < |s| {
        var newConsecutiveX := if s[pos] == 'x' then consecutiveX + 1 else 0;
        CountExcessivePositionsHelperLemma(s, pos + 1, newConsecutiveX);
    }
}

function CountExcessivePositionsFunction(s: string, pos: int, consecutiveX: int): int
    requires 0 <= pos <= |s|
    requires consecutiveX >= 0
    decreases |s| - pos
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
    var currentResult := 0;
    var consecutiveX := 0;
    // The loop iterates from i = 0 to i = |s|.
    // When i is the current index, we are calculating the state *before* processing s[i].
    // After the loop body, i is incremented, and then the next iteration starts.
    // The invariant must hold *before* checking the loop condition and *after* the loop body.
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant consecutiveX >= 0
        invariant currentResult >= 0
        invariant currentResult <= i
        invariant (i == 0 ==> consecutiveX == 0)
        invariant CountExcessivePositionsFunction(s, 0, 0) == currentResult + CountExcessivePositionsFunction(s, i, consecutiveX)
    {
        if i < |s| {
            var newConsecutiveX := if s[i] == 'x' then consecutiveX + 1 else 0;
            var currentContribution := if newConsecutiveX > 2 then 1 else 0;
            currentResult := currentResult + currentContribution;
            consecutiveX := newConsecutiveX;
        }
    }
    // After the loop, `i == |s|`.
    // From the invariant: `CountExcessivePositionsFunction(s, 0, 0) == currentResult + CountExcessivePositionsFunction(s, |s|, consecutiveX)`.
    // We know `CountExcessivePositionsFunction(s, |s|, consecutiveX) == 0`.
    // So `CountExcessivePositionsFunction(s, 0, 0) == currentResult`.
    // By `CountExcessivePositionsHelperLemma`, we know `CountExcessivePositionsHelper(s, 0, 0) == CountExcessivePositionsFunction(s, 0, 0)`.
    // And `CountExcessivePositions(s)` is defined as `CountExcessivePositionsHelper(s, 0, 0)`.
    // Therefore, `currentResult == CountExcessivePositions(s)`.
    CountExcessivePositionsHelperLemma(s, 0, 0); 
    result := currentResult;
}
// </vc-code>

