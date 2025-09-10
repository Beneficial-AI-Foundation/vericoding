predicate ValidInput(a: int, b: int, c: int, d: int)
{
    0 <= a < b <= 100 && 0 <= c < d <= 100
}

function min(x: int, y: int): int
{
    if x < y then x else y
}

function max(x: int, y: int): int
{
    if x > y then x else y
}

function IntervalOverlapLength(a: int, b: int, c: int, d: int): int
{
    if min(b, d) - max(a, c) > 0 then min(b, d) - max(a, c) else 0
}

// <vc-helpers>
lemma IntervalOverlapProperties(a: int, b: int, c: int, d: int)
    requires ValidInput(a, b, c, d)
    ensures IntervalOverlapLength(a, b, c, d) >= 0
    ensures IntervalOverlapLength(a, b, c, d) <= min(b - a, d - c)
    ensures IntervalOverlapLength(a, b, c, d) <= 100
{
    var overlap := min(b, d) - max(a, c);
    if overlap > 0 {
        assert max(a, c) >= a && max(a, c) >= c;
        assert min(b, d) <= b && min(b, d) <= d;
        assert overlap <= b - a && overlap <= d - c;
        assert b - a <= 100 && d - c <= 100;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, c: int, d: int) returns (result: int)
    requires ValidInput(a, b, c, d)
    ensures result >= 0
    ensures result == IntervalOverlapLength(a, b, c, d)
    ensures result <= 100
// </vc-spec>
// <vc-code>
{
    var overlap := min(b, d) - max(a, c);
    if overlap > 0 {
        result := overlap;
    } else {
        result := 0;
    }
    IntervalOverlapProperties(a, b, c, d);
}
// </vc-code>

