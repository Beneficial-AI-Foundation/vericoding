predicate ValidInput(W: int, a: int, b: int)
{
    W >= 1 && a >= 1 && b >= 1
}

function AbsDiff(x: int, y: int): int
{
    if x >= y then x - y else y - x
}

function MinMoveDistance(W: int, a: int, b: int): int
    requires ValidInput(W, a, b)
{
    var distance := AbsDiff(a, b);
    if distance <= W then 0
    else distance - W
}

predicate RectanglesConnect(W: int, a: int, b: int)
    requires ValidInput(W, a, b)
{
    AbsDiff(a, b) <= W
}

// <vc-helpers>
lemma lemma_MinMoveDistance_NonNegative(W: int, a: int, b: int)
    requires ValidInput(W, a, b)
    ensures MinMoveDistance(W, a, b) >= 0
{
    var distance := AbsDiff(a, b);
    if distance <= W {
        assert MinMoveDistance(W, a, b) == 0;
    } else {
        assert MinMoveDistance(W, a, b) == distance - W;
        assert distance - W >= 0; // Since distance > W
    }
}

lemma lemma_MinMoveDistance_RectanglesConnect(W: int, a: int, b: int)
    requires ValidInput(W, a, b)
    ensures RectanglesConnect(W, a, b) <== MinMoveDistance(W, a, b) == 0
{
    var distance := AbsDiff(a, b);
    if distance <= W {
        // RectanglesConnect(W, a, b) is true
        // MinMoveDistance(W, a, b) is 0
        assert RectanglesConnect(W, a, b);
        assert MinMoveDistance(W, a, b) == 0;
    } else {
        // RectanglesConnect(W, a, b) is false
        // MinMoveDistance(W, a, b) is distance - W (which is > 0)
        assert !RectanglesConnect(W, a, b);
        assert MinMoveDistance(W, a, b) == distance - W;
        assert MinMoveDistance(W, a, b) > 0;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(W: int, a: int, b: int) returns (result: int)
    requires ValidInput(W, a, b)
    ensures result == MinMoveDistance(W, a, b)
    ensures result >= 0
    ensures RectanglesConnect(W, a, b) <==> result == 0
// </vc-spec>
// <vc-code>
{
    var distance := AbsDiff(a, b);
    if distance <= W {
        result := 0;
    } else {
        result := distance - W;
    }

    // Proofs for post-conditions
    lemma_MinMoveDistance_NonNegative(W, a, b);
    lemma_MinMoveDistance_RectanglesConnect(W, a, b);
}
// </vc-code>

