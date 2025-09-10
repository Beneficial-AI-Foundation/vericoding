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
lemma CountExcessivePositionsHelperLemma(s: string, pos: int, consecutiveX: int)
    requires 0 <= pos <= |s|
    requires consecutiveX >= 0
    ensures CountExcessivePositionsHelper(s, pos, consecutiveX) >= 0
    decreases |s| - pos
{
    if pos < |s| {
        var newConsecutiveX := if s[pos] == 'x' then consecutiveX + 1 else 0;
        CountExcessivePositionsHelperLemma(s, pos + 1, newConsecutiveX);
    }
}

lemma CountExcessivePositionsHelperStep(s: string, pos: int, consecutiveX: int)
    requires 0 <= pos < |s|
    requires consecutiveX >= 0
    ensures CountExcessivePositionsHelper(s, pos, consecutiveX) == 
        (if (if s[pos] == 'x' then consecutiveX + 1 else 0) > 2 then 1 else 0) + 
        CountExcessivePositionsHelper(s, pos + 1, if s[pos] == 'x' then consecutiveX + 1 else 0)
    decreases |s| - pos
{
    // This lemma is trivial from the function definition
}

lemma ConsecutiveXCountLemma(s: string, pos: int) 
    requires 0 <= pos <= |s|
    ensures ConsecutiveXCount(s, pos) >= 0
    decreases pos
{
    if pos > 0 {
        ConsecutiveXCountLemma(s, pos - 1);
    }
}

lemma CountExcessivePositionsHelperBase(s: string, consecutiveX: int)
    requires consecutiveX >= 0
    ensures CountExcessivePositionsHelper(s, |s|, consecutiveX) == 0
{
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
    result := 0;
    var consecutiveX := 0;
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant consecutiveX >= 0
        invariant result >= 0
        invariant result + CountExcessivePositionsHelper(s, i, consecutiveX) == CountExcessivePositions(s)
        decreases |s| - i
    {
        var oldConsecutiveX := consecutiveX;
        var oldResult := result;
        
        if s[i] == 'x' {
            consecutiveX := consecutiveX + 1;
        } else {
            consecutiveX := 0;
        }
        
        if consecutiveX > 2 {
            result := result + 1;
        }
        
        CountExcessivePositionsHelperStep(s, i, oldConsecutiveX);
        assert CountExcessivePositionsHelper(s, i, oldConsecutiveX) == 
            (if consecutiveX > 2 then 1 else 0) + CountExcessivePositionsHelper(s, i + 1, consecutiveX);
        assert oldResult + CountExcessivePositionsHelper(s, i, oldConsecutiveX) == CountExcessivePositions(s);
        assert result == oldResult + (if consecutiveX > 2 then 1 else 0);
        assert result + CountExcessivePositionsHelper(s, i + 1, consecutiveX) == CountExcessivePositions(s);
        
        i := i + 1;
    }
    
    CountExcessivePositionsHelperBase(s, consecutiveX);
    assert CountExcessivePositionsHelper(s, i, consecutiveX) == 0;
}
// </vc-code>

