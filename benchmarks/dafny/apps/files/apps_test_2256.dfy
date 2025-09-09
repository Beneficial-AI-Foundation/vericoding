Given n students in positions 1 to n, with two rival students initially at positions a and b,
find the maximum distance between the rivals after performing at most x adjacent swaps.
Distance between positions p and s is |p - s|.

predicate ValidInput(n: int, x: int, a: int, b: int)
{
    2 <= n <= 100 && 0 <= x <= 100 && 1 <= a <= n && 1 <= b <= n && a != b
}

function MaxDistance(n: int, x: int, a: int, b: int): int
    requires ValidInput(n, x, a, b)
{
    var initialDistance := if a >= b then a - b else b - a;
    var maxPossibleDistance := initialDistance + x;
    var maxLineDistance := n - 1;
    if maxPossibleDistance <= maxLineDistance then maxPossibleDistance else maxLineDistance
}

predicate ValidResult(n: int, x: int, a: int, b: int, result: int)
    requires ValidInput(n, x, a, b)
{
    result == MaxDistance(n, x, a, b) && 0 <= result <= n - 1
}

function Abs(x: int): int
{
    if x >= 0 then x else -x
}

function Min(a: int, b: int): int
{
    if a <= b then a else b
}

method SolveRivalDistance(n: int, x: int, a: int, b: int) returns (result: int)
    requires ValidInput(n, x, a, b)
    ensures ValidResult(n, x, a, b, result)
    ensures result >= 0
{
    var initialDistance := Abs(a - b);
    var maxPossibleDistance := initialDistance + x;
    result := Min(maxPossibleDistance, n - 1);
}
