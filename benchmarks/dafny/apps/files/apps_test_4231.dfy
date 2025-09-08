Given an H×W grid of white cells, choose h rows and w columns to paint black.
All cells that are either in a chosen row OR in a chosen column will be painted black.
Determine how many white cells remain after painting.

predicate ValidInput(H: int, W: int, h: int, w: int)
{
    1 <= H <= 20 && 1 <= W <= 20 && 1 <= h <= H && 1 <= w <= W
}

function WhiteCellsRemaining(H: int, W: int, h: int, w: int): int
    requires ValidInput(H, W, h, w)
{
    (H - h) * (W - w)
}

method solve(H: int, W: int, h: int, w: int) returns (result: int)
    requires ValidInput(H, W, h, w)
    ensures result == WhiteCellsRemaining(H, W, h, w)
    ensures result >= 0
{
    result := (H - h) * (W - w);
}
