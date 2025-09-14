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
  var pos := 0;
  var consecutiveX := 0;
  result := 0;
  while pos < |s|
    invariant 0 <= pos <= |s|
    invariant consecutiveX >= 0
    invariant result >= 0
    invariant result <= pos
    invariant result + CountExcessivePositionsHelper(s, pos, consecutiveX) == CountExcessivePositions(s)
    decreases |s| - pos
  {
    var newConsecutiveX := if s[pos] == 'x' then consecutiveX + 1 else 0;
    var contrib := if newConsecutiveX > 2 then 1 else 0;
    reveal CountExcessivePositionsHelper();
    assert CountExcessivePositionsHelper(s, pos, consecutiveX) ==
           contrib + CountExcessivePositionsHelper(s, pos + 1, newConsecutiveX);
    result := result + contrib;
    pos := pos + 1;
    consecutiveX := newConsecutiveX;
  }
  assert pos == |s|;
  reveal CountExcessivePositionsHelper();
  assert CountExcessivePositionsHelper(s, pos, consecutiveX) == 0;
}
// </vc-code>

