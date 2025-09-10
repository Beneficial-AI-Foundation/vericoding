predicate ValidInput(x1: int, y1: int, x2: int, y2: int)
{
    -100 <= x1 <= 100 && -100 <= y1 <= 100 && -100 <= x2 <= 100 && -100 <= y2 <= 100
}

predicate IsInvalidCase(x1: int, y1: int, x2: int, y2: int)
{
    x1 != x2 && y1 != y2 && abs(x1 - x2) != abs(y1 - y2)
}

predicate IsDiagonalCase(x1: int, y1: int, x2: int, y2: int)
{
    x1 != x2 && y1 != y2 && abs(x1 - x2) == abs(y1 - y2)
}

predicate IsVerticalEdgeCase(x1: int, y1: int, x2: int, y2: int)
{
    x1 == x2
}

predicate IsHorizontalEdgeCase(x1: int, y1: int, x2: int, y2: int)
{
    x1 != x2 && y1 == y2
}

function ExpectedDiagonalResult(x1: int, y1: int, x2: int, y2: int): seq<int>
{
    [x1, y2, x2, y1]
}

function ExpectedVerticalResult(x1: int, y1: int, x2: int, y2: int): seq<int>
{
    [x1 + abs(y2 - y1), y1, x1 + abs(y2 - y1), y2]
}

function ExpectedHorizontalResult(x1: int, y1: int, x2: int, y2: int): seq<int>
{
    [x1, y1 + abs(x2 - x1), x2, y1 + abs(x2 - x1)]
}

predicate ValidOutput(result: seq<int>)
{
    (|result| == 1 && result[0] == -1) ||
    (|result| == 4 && (forall i :: 0 <= i < 4 ==> -1000 <= result[i] <= 1000))
}

// <vc-helpers>
function Abs(a: int): int
{
  if a < 0 then -a else a
}
// </vc-helpers>

// <vc-spec>
method solve(x1: int, y1: int, x2: int, y2: int) returns (result: seq<int>)
    requires ValidInput(x1, y1, x2, y2)
    ensures ValidOutput(result)
    ensures IsInvalidCase(x1, y1, x2, y2) ==> result == [-1]
    ensures IsDiagonalCase(x1, y1, x2, y2) ==> result == ExpectedDiagonalResult(x1, y1, x2, y2)
    ensures IsVerticalEdgeCase(x1, y1, x2, y2) ==> result == ExpectedVerticalResult(x1, y1, x2, y2)
    ensures IsHorizontalEdgeCase(x1, y1, x2, y2) ==> result == ExpectedHorizontalResult(x1, y1, x2, y2)
// </vc-spec>
// <vc-code>
{
    if IsInvalidCase(x1, y1, x2, y2)
    {
        result := [-1];
    }
    else if IsDiagonalCase(x1, y1, x2, y2)
    {
        result := ExpectedDiagonalResult(x1, y1, x2, y2);
    }
    else if IsVerticalEdgeCase(x1, y1, x2, y2)
    {
        result := ExpectedVerticalResult(x1, y1, x2, y2);
    }
    else if IsHorizontalEdgeCase(x1, y1, x2, y2)
    {
        result := ExpectedHorizontalResult(x1, y1, x2, y2);
    }
    else
        // This case covers x1 == x2 && y1 == y2, where starting and ending points are the same.
        // It's not explicitly covered by the ensures clauses to provide a specific result,
        // but it must return a valid output according to ValidOutput.
        // The problem statement implies these 4 cases cover all valid inputs that need specific calculation.
        // When x1==x2 && y1==y2, any valid output like [-1] or [x1, y1, x1, y1] would satisfy ValidOutput
        // and not contradict the specific ensures clauses (as their premises are false).
        // Let's return [-1] for simplicity, as it's a valid output and signifies no geometric shape.
    {
        result := [-1];
    }
}
// </vc-code>

