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
    decreases |s| - pos
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
    // The invariant for currentResult needs to represent the sum of contributions *up to* i-1.
    // The loop calculates contribution for s[i] and adds it to currentResult.
    // The CountExcessivePositionsHelper is a recursive definition, so its value at (s, 0, 0) is the total.
    // The loop calculates the result iteratively, so we need to bridge the two.
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant consecutiveX >= 0
        invariant currentResult >= 0
        invariant (i == 0 ==> currentResult == 0 && consecutiveX == 0)
        // The invariant should state that `currentResult` accumulates the contributions
        // for `s[0]` through `s[i-1]`.
        // The `CountExcessivePositionsFunction(s, 0, 0)` is the total expected count.
        // The `CountExcessivePositionsFunction(s, i, consecutiveX)` represents the remaining
        // count from index `i` onwards, given the `consecutiveX` count until `i-1`.
        invariant currentResult == CountExcessivePositionsFunction(s, 0, 0) - CountExcessivePositionsFunction(s, i, consecutiveX)
    {
        if i < |s| {
            var newConsecutiveX := if s[i] == 'x' then consecutiveX + 1 else 0;
            var currentContribution := if newConsecutiveX > 2 then 1 else 0;
            currentResult := currentResult + currentContribution;
            consecutiveX := newConsecutiveX;
        }
    }
    // After the loop, i == |s|.
    // From the invariant: currentResult == CountExcessivePositionsFunction(s, 0, 0) - CountExcessivePositionsFunction(s, |s|, consecutiveX)
    // We know CountExcessivePositionsFunction(s, |s|, consecutiveX) == 0.
    // So currentResult == CountExcessivePositionsFunction(s, 0, 0).
    // And by the lemma, CountExcessivePositionsFunction(s, 0, 0) == CountExcessivePositionsHelper(s, 0, 0).
    // And CountExcessivePositionsHelper(s, 0, 0) is CountExcessivePositions(s).
    // So currentResult == CountExcessivePositions(s).
    CountExcessivePositionsHelperLemma(s, 0, 0); // This links the recursive helper to the function.
    result := currentResult;
}
// </vc-code>

