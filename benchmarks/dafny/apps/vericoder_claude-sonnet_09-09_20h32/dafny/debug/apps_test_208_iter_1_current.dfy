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
lemma abs_properties(a: int, b: int)
    ensures abs(a) >= 0
    ensures abs(a - b) == abs(b - a)
    ensures abs(a) <= 100 ==> -1000 <= a <= 1000
{
}

lemma diagonal_result_bounds(x1: int, y1: int, x2: int, y2: int)
    requires ValidInput(x1, y1, x2, y2)
    requires IsDiagonalCase(x1, y1, x2, y2)
    ensures var result := ExpectedDiagonalResult(x1, y1, x2, y2);
            |result| == 4 && (forall i :: 0 <= i < 4 ==> -1000 <= result[i] <= 1000)
{
}

lemma vertical_result_bounds(x1: int, y1: int, x2: int, y2: int)
    requires ValidInput(x1, y1, x2, y2)
    requires IsVerticalEdgeCase(x1, y1, x2, y2)
    ensures var result := ExpectedVerticalResult(x1, y1, x2, y2);
            |result| == 4 && (forall i :: 0 <= i < 4 ==> -1000 <= result[i] <= 1000)
{
    abs_properties(y2, y1);
    assert abs(y2 - y1) <= 200;
    assert x1 + abs(y2 - y1) <= 100 + 200;
}

lemma horizontal_result_bounds(x1: int, y1: int, x2: int, y2: int)
    requires ValidInput(x1, y1, x2, y2)
    requires IsHorizontalEdgeCase(x1, y1, x2, y2)
    ensures var result := ExpectedHorizontalResult(x1, y1, x2, y2);
            |result| == 4 && (forall i :: 0 <= i < 4 ==> -1000 <= result[i] <= 1000)
{
    abs_properties(x2, x1);
    assert abs(x2 - x1) <= 200;
    assert y1 + abs(x2 - x1) <= 100 + 200;
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
    if IsInvalidCase(x1, y1, x2, y2) {
        result := [-1];
    } else if IsDiagonalCase(x1, y1, x2, y2) {
        diagonal_result_bounds(x1, y1, x2, y2);
        result := ExpectedDiagonalResult(x1, y1, x2, y2);
    } else if IsVerticalEdgeCase(x1, y1, x2, y2) {
        vertical_result_bounds(x1, y1, x2, y2);
        result := ExpectedVerticalResult(x1, y1, x2, y2);
    } else {
        assert IsHorizontalEdgeCase(x1, y1, x2, y2);
        horizontal_result_bounds(x1, y1, x2, y2);
        result := ExpectedHorizontalResult(x1, y1, x2, y2);
    }
}
// </vc-code>

