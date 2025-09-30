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
lemma IntervalOverlapBound(a: int, b: int, c: int, d: int)
    requires ValidInput(a, b, c, d)
    ensures IntervalOverlapLength(a, b, c, d) <= 100
{
    if min(b, d) - max(a, c) > 0 {
        assert min(b, d) <= 100;
        assert max(a, c) >= 0;
        assert IntervalOverlapLength(a, b, c, d) == min(b, d) - max(a, c);
        assert IntervalOverlapLength(a, b, c, d) <= 100 - 0;
    } else {
        assert IntervalOverlapLength(a, b, c, d) == 0;
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
    var minEnd := min(b, d);
    var maxStart := max(a, c);
    
    if minEnd - maxStart > 0 {
        result := minEnd - maxStart;
    } else {
        result := 0;
    }
    
    IntervalOverlapBound(a, b, c, d);
}
// </vc-code>

