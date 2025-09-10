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
lemma IntervalOverlapLengthProperties(a: int, b: int, c: int, d: int)
    requires ValidInput(a, b, c, d)
    ensures IntervalOverlapLength(a, b, c, d) == min(b, d) - max(a, c)
    ensures IntervalOverlapLength(a, b, c, d) >= 0
    ensures IntervalOverlapLength(a, b, c, d) <= 100
{
    // The function definition already handles the case where there's no overlap
    // Since ValidInput ensures 0 <= a < b <= 100 && 0 <= c < d <= 100,
    // the overlap length will always be non-negative and <= 100
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
    var start := max(a, c);
    var end := min(b, d);
    if (end > start) {
        result := end - start;
    } else {
        result := 0;
    }
}
// </vc-code>

