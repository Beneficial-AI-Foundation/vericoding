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

// <vc-helpers>
lemma MaxDistanceProperties(n: int, x: int, a: int, b: int)
    requires ValidInput(n, x, a, b)
    ensures 0 <= MaxDistance(n, x, a, b) <= n - 1
{
    var initialDistance := if a >= b then a - b else b - a;
    var maxPossibleDistance := initialDistance + x;
    var maxLineDistance := n - 1;
    
    assert initialDistance >= 0;
    assert maxPossibleDistance >= initialDistance;
    assert maxLineDistance == n - 1 >= 0;
    
    if maxPossibleDistance <= maxLineDistance {
        assert MaxDistance(n, x, a, b) == maxPossibleDistance;
        assert MaxDistance(n, x, a, b) >= 0;
        assert MaxDistance(n, x, a, b) <= maxLineDistance;
    } else {
        assert MaxDistance(n, x, a, b) == maxLineDistance;
        assert MaxDistance(n, x, a, b) == n - 1;
        assert 0 <= MaxDistance(n, x, a, b) <= n - 1;
    }
}
// </vc-helpers>

// <vc-spec>
method SolveRivalDistance(n: int, x: int, a: int, b: int) returns (result: int)
    requires ValidInput(n, x, a, b)
    ensures ValidResult(n, x, a, b, result)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    var initialDistance: int;
    if a >= b {
        initialDistance := a - b;
    } else {
        initialDistance := b - a;
    }
    
    var maxPossibleDistance := initialDistance + x;
    var maxLineDistance := n - 1;
    
    if maxPossibleDistance <= maxLineDistance {
        result := maxPossibleDistance;
    } else {
        result := maxLineDistance;
    }
    
    MaxDistanceProperties(n, x, a, b);
}
// </vc-code>

