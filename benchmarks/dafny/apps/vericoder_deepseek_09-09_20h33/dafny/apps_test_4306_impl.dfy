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
    // Proof that max(a, c) < min(b, d) under ValidInput
    assert max(a, c) < min(b, d) by {
        assert a < b && c < d;
        if a >= c {
            assert max(a, c) == a;
            assert a < b;
            assert min(b, d) <= b;
            assert a < min(b, d) || (min(b, d) == b && a < b);
        } else {
            assert max(a, c) == c;
            assert c < d;
            assert min(b, d) <= d;
            assert c < min(b, d) || (min(b, d) == d && c < d);
        }
    }
    assert min(b, d) - max(a, c) > 0;
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
    // Postcondition proof
    assert result == min(b, d) - max(a, c) by {
        if (end > start) {
            assert result == end - start;
            assert end == min(b, d) && start == max(a, c);
        } else {
            assert result == 0;
            IntervalOverlapLengthProperties(a, b, c, d);
            assert min(b, d) - max(a, c) >= 0;
            assert end <= start;
            assert min(b, d) - max(a, c) == 0;
        }
    }
}
// </vc-code>

