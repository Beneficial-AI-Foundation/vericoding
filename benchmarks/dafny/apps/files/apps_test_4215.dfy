Given a window of width A and two curtains each of horizontal length B,
determine the minimum total horizontal length of the uncovered part when 
the curtains are optimally positioned to minimize uncovered area.

predicate ValidInput(a: int, b: int)
{
    1 <= a <= 100 && 1 <= b <= 100
}

function UncoveredLength(a: int, b: int): int
{
    max(0, a - 2 * b)
}

function max(x: int, y: int): int
{
    if x >= y then x else y
}

method solve(a: int, b: int) returns (result: int)
    requires ValidInput(a, b)
    ensures result >= 0
    ensures result == UncoveredLength(a, b)
    ensures result == if a > 2 * b then a - 2 * b else 0
{
    if a > 2 * b {
        result := a - 2 * b;
    } else {
        result := 0;
    }
}
