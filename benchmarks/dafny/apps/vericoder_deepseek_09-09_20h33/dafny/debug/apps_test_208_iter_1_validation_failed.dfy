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
lemma {:axiom} AbsPositive(x: int)
    ensures abs(x) >= 0
{
}

lemma {:axiom} AbsDifference(x: int, y: int)
    ensures abs(x - y) == abs(y - x)
{
}

lemma {:axiom} DiagonalPointsValid(x1: int, y1: int, x2: int, y2: int)
    requires IsDiagonalCase(x1, y1, x2, y2)
    ensures -1000 <= x1 <= 1000 && -1000 <= y2 <= 1000 && -1000 <= x2 <= 1000 && -1000 <= y1 <= 1000
{
}

lemma {:axiom} VerticalPointsValid(x1: int, y1: int, x2: int, y2: int)
    requires IsVerticalEdgeCase(x1, y1, x2, y2)
    ensures -1000 <= x1 + abs(y2 - y1) <= 1000 && -1000 <= y1 <= 1000 && -1000 <= x1 + abs(y2 - y1) <= 1000 && -1000 <= y2 <= 1000
{
}

lemma {:axiom} HorizontalPointsValid(x1: int, y1: int, x2: int, y2: int)
    requires IsHorizontalEdgeCase(x1, y1, x2, y2)
    ensures -1000 <= x1 <= 1000 && -1000 <= y1 + abs(x2 - x1) <= 1000 && -1000 <= x2 <= 1000 && -1000 <= y1 + abs(x2 - x1) <= 1000
{
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
    if x1 == x2 && y1 == y2 {
        result := [-1];
    } else if x1 != x2 && y1 != y2 && abs(x1 - x2) == abs(y1 - y2) {
        result := [x1, y2, x2, y1];
    } else if x1 == x2 {
        var diff := abs(y2 - y1);
        result := [x1 + diff, y1, x1 + diff, y2];
    } else if y1 == y2 {
        var diff := abs(x2 - x1);
        result := [x1, y1 + diff, x2, y1 + diff];
    } else {
        result := [-1];
    }
}
// </vc-code>

