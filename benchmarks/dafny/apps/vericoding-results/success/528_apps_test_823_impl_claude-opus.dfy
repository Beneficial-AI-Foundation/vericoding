predicate ValidInput(x: int, y: int) {
    -100 <= x <= 100 && -100 <= y <= 100
}

predicate IsOriginOrFirstPoint(x: int, y: int) {
    (x == 0 && y == 0) || (x == 1 && y == 0)
}

predicate IsRightEdge(x: int, y: int) {
    x >= 1 && -x + 1 < y <= x
}

predicate IsLeftEdge(x: int, y: int) {
    x < 0 && x <= y < -x
}

predicate IsTopEdge(x: int, y: int) {
    y > 0 && -y <= x < y
}

function ComputeTurns(x: int, y: int): int
    requires ValidInput(x, y)
{
    if IsOriginOrFirstPoint(x, y) then 0
    else if IsRightEdge(x, y) then 1 + 4 * (x - 1)
    else if IsLeftEdge(x, y) then 3 + 4 * (-x - 1)
    else if IsTopEdge(x, y) then 2 + 4 * (y - 1)
    else -4 * y
}

// <vc-helpers>
lemma ComputeTurnsNonNegative(x: int, y: int)
    requires ValidInput(x, y)
    ensures ComputeTurns(x, y) >= 0
{
    if IsOriginOrFirstPoint(x, y) {
        assert ComputeTurns(x, y) == 0;
    } else if IsRightEdge(x, y) {
        assert x >= 1;
        assert ComputeTurns(x, y) == 1 + 4 * (x - 1);
        assert ComputeTurns(x, y) >= 1;
    } else if IsLeftEdge(x, y) {
        assert x < 0;
        assert -x - 1 >= 0;
        assert ComputeTurns(x, y) == 3 + 4 * (-x - 1);
        assert ComputeTurns(x, y) >= 3;
    } else if IsTopEdge(x, y) {
        assert y > 0;
        assert y - 1 >= 0;
        assert ComputeTurns(x, y) == 2 + 4 * (y - 1);
        assert ComputeTurns(x, y) >= 2;
    } else {
        assert ComputeTurns(x, y) == -4 * y;
        // In this case, we need to show y <= 0
        // If not any of the above cases, and y > 0, we'd be in IsTopEdge
        // So y must be <= 0
        assert y <= 0;
        assert -4 * y >= 0;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(x: int, y: int) returns (result: int)
    requires ValidInput(x, y)
    ensures result >= 0
    ensures result == ComputeTurns(x, y)
    ensures IsOriginOrFirstPoint(x, y) ==> result == 0
    ensures IsRightEdge(x, y) ==> result == 1 + 4 * (x - 1)
    ensures IsLeftEdge(x, y) ==> result == 3 + 4 * (-x - 1)
    ensures IsTopEdge(x, y) ==> result == 2 + 4 * (y - 1)
    ensures !(IsOriginOrFirstPoint(x, y) || IsRightEdge(x, y) || IsLeftEdge(x, y) || IsTopEdge(x, y)) ==> result == -4 * y
// </vc-spec>
// <vc-code>
{
    ComputeTurnsNonNegative(x, y);
    
    if IsOriginOrFirstPoint(x, y) {
        result := 0;
    } else if IsRightEdge(x, y) {
        result := 1 + 4 * (x - 1);
    } else if IsLeftEdge(x, y) {
        result := 3 + 4 * (-x - 1);
    } else if IsTopEdge(x, y) {
        result := 2 + 4 * (y - 1);
    } else {
        result := -4 * y;
    }
}
// </vc-code>

