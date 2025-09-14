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
function abs(x: int): int {
    if x < 0 then -x else x
}

lemma VerticalResultBounds(x1: int, y1: int, x2: int, y2: int)
    requires ValidInput(x1, y1, x2, y2)
    ensures forall i :: 0 <= i < 4 ==> -1000 <= ExpectedVerticalResult(x1, y1, x2, y2)[i] <= 1000
{
    var d := abs(y2 - y1);
    assert -200 <= y2 - y1 <= 200;
    assert 0 <= d <= 200;
    var a := x1 + d;
    assert -100 <= a <= 300;
    assert -1000 <= a <= 1000;
    assert -1000 <= y1 <= 1000;
    assert -1000 <= y2 <= 1000;
    var r := ExpectedVerticalResult(x1, y1, x2, y2);
    assert r[0] == a;
    assert r[1] == y1;
    assert r[2] == a;
    assert r[3] == y2;
    assert -1000 <= r[0] <= 1000;
    assert -1000 <= r[1] <= 1000;
    assert -1000 <= r[2] <= 1000;
    assert -1000 <= r[3] <= 1000;
}

lemma HorizontalResultBounds(x1: int, y1: int, x2: int, y2: int)
    requires ValidInput(x1, y1, x2, y2)
    ensures forall i :: 0 <= i < 4 ==> -1000 <= ExpectedHorizontalResult(x1, y1, x2, y2)[i] <= 1000
{
    var d := abs(x2 - x1);
    assert -200 <= x2 - x1 <= 200;
    assert 0 <= d <= 200;
    var b := y1 + d;
    assert -100 <= b <= 300;
    assert -1000 <= b <= 1000;
    assert -1000 <= x1 <= 1000;
    assert -1000 <= x2 <= 1000;
    var r := ExpectedHorizontalResult(x1, y1, x2, y2);
    assert r[0] == x1;
    assert r[1] == b;
    assert r[2] == x2;
    assert r[3] == b;
    assert -1000 <= r[0] <= 1000;
    assert -1000 <= r[1] <= 1000;
    assert -1000 <= r[2] <= 1000;
    assert -1000 <= r[3] <= 1000;
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
        return [-1];
    } else if IsDiagonalCase(x1, y1, x2, y2) {
        return ExpectedDiagonalResult(x1, y1, x2, y2);
    } else if IsVerticalEdgeCase(x1, y1, x2, y2) {
        VerticalResultBounds(x1, y1, x2, y2);
        return ExpectedVerticalResult(x1, y1, x2, y2);
    } else {
        HorizontalResultBounds(x1, y1, x2, y2);
        return ExpectedHorizontalResult(x1, y1, x2, y2);
    }
}
// </vc-code>

