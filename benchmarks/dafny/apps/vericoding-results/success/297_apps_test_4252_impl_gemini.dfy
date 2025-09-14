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
  result := 0;
  var i := 0;
  var consecutiveX := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant result >= 0
    invariant result <= i
    invariant consecutiveX >= 0
    invariant result + CountExcessivePositionsHelper(s, i, consecutiveX) == CountExcessivePositions(s)
    invariant consecutiveX == ConsecutiveXCount(s, i)
  {
    var newConsecutiveX := if s[i] == 'x' then consecutiveX + 1 else 0;

    if newConsecutiveX > 2 {
      result := result + 1;
    }

    consecutiveX := newConsecutiveX;
    i := i + 1;
  }
}
// </vc-code>

