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
lemma CountExcessivePositionsEquivalence(s: string, pos: int, consecutiveX: int, accumulated: int)
    requires 0 <= pos <= |s|
    requires consecutiveX >= 0
    requires accumulated >= 0
    ensures CountExcessivePositionsHelper(s, pos, consecutiveX) + accumulated == 
            accumulated + CountExcessivePositionsHelper(s, pos, consecutiveX)
{
    // Trivial commutativity
}

lemma CountExcessivePositionsHelperAccumulation(s: string, i: int, consecutiveX: int)
    requires 0 <= i < |s|
    requires consecutiveX >= 0
    ensures CountExcessivePositionsHelper(s, i, consecutiveX) ==
            (if s[i] == 'x' then
                (if consecutiveX + 1 > 2 then 1 else 0) + CountExcessivePositionsHelper(s, i + 1, consecutiveX + 1)
            else
                CountExcessivePositionsHelper(s, i + 1, 0))
{
    var newConsecutiveX := if s[i] == 'x' then consecutiveX + 1 else 0;
    var currentContribution := if newConsecutiveX > 2 then 1 else 0;
    assert CountExcessivePositionsHelper(s, i, consecutiveX) == 
           currentContribution + CountExcessivePositionsHelper(s, i + 1, newConsecutiveX);
}

lemma CountExcessivePositionsHelperBound(s: string, pos: int, consecutiveX: int)
    requires 0 <= pos <= |s|
    requires consecutiveX >= 0
    ensures CountExcessivePositionsHelper(s, pos, consecutiveX) <= |s| - pos
    decreases |s| - pos
{
    if pos >= |s| {
        assert CountExcessivePositionsHelper(s, pos, consecutiveX) == 0;
        assert 0 <= |s| - pos;
    } else {
        var newConsecutiveX := if s[pos] == 'x' then consecutiveX + 1 else 0;
        var currentContribution := if newConsecutiveX > 2 then 1 else 0;
        
        assert currentContribution <= 1;
        CountExcessivePositionsHelperBound(s, pos + 1, newConsecutiveX);
        assert CountExcessivePositionsHelper(s, pos + 1, newConsecutiveX) <= |s| - (pos + 1);
        assert currentContribution + CountExcessivePositionsHelper(s, pos + 1, newConsecutiveX) <= 1 + (|s| - pos - 1);
        assert 1 + (|s| - pos - 1) == |s| - pos;
    }
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
    var i := 0;
    var consecutiveX := 0;
    result := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant consecutiveX >= 0
        invariant result >= 0
        invariant result + CountExcessivePositionsHelper(s, i, consecutiveX) == CountExcessivePositions(s)
        invariant result <= i
    {
        var oldResult := result;
        var oldConsecutiveX := consecutiveX;
        
        if s[i] == 'x' {
            consecutiveX := consecutiveX + 1;
            if consecutiveX > 2 {
                result := result + 1;
            }
        } else {
            consecutiveX := 0;
        }
        
        // Prove invariant maintenance
        assert CountExcessivePositionsHelper(s, i, oldConsecutiveX) ==
               (if s[i] == 'x' then
                   (if oldConsecutiveX + 1 > 2 then 1 else 0) + CountExcessivePositionsHelper(s, i + 1, oldConsecutiveX + 1)
               else
                   CountExcessivePositionsHelper(s, i + 1, 0));
        
        assert result <= i + 1;
        i := i + 1;
    }
    
    assert i == |s|;
    assert CountExcessivePositionsHelper(s, |s|, consecutiveX) == 0;
    assert result == CountExcessivePositions(s);
    assert result <= |s|;
}
// </vc-code>

