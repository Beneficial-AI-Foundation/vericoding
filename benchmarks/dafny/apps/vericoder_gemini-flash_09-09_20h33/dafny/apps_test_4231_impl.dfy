predicate ValidInput(H: int, W: int, h: int, w: int)
{
    1 <= H <= 20 && 1 <= W <= 20 && 1 <= h <= H && 1 <= w <= W
}

function WhiteCellsRemaining(H: int, W: int, h: int, w: int): int
    requires ValidInput(H, W, h, w)
{
    (H - h) * (W - w)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(H: int, W: int, h: int, w: int) returns (result: int)
    requires ValidInput(H, W, h, w)
    ensures result == WhiteCellsRemaining(H, W, h, w)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    result := (H - h) * (W - w);
}
// </vc-code>

