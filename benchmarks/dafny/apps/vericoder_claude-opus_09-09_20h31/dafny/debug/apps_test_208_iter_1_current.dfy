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
function abs(x: int): int
{
    if x < 0 then -x else x
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
    if x1 != x2 && y1 != y2 && abs(x1 - x2) != abs(y1 - y2) {
        // Invalid case - cannot form a square
        result := [-1];
    } else if x1 != x2 && y1 != y2 && abs(x1 - x2) == abs(y1 - y2) {
        // Diagonal case - return the other two corners
        result := [x1, y2, x2, y1];
    } else if x1 == x2 {
        // Vertical edge case
        var side_length := abs(y2 - y1);
        result := [x1 + side_length, y1, x1 + side_length, y2];
    } else {
        // Horizontal edge case (x1 != x2 && y1 == y2)
        var side_length := abs(x2 - x1);
        result := [x1, y1 + side_length, x2, y1 + side_length];
    }
}
// </vc-code>

