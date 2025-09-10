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
    // Proof that min(b, d) - max(a, c) is always non-negative under ValidInput
    assert max(a, c) <= min(b, d) by {
        assert a <= b && c <= d;
        assert max(a, c) >= a && max(a, c) >= c;
        assert min(b, d) <= b && min(b, d) <= d;
        assert max(a, c) <= b && max(a, c) <= d;  // Since a < b and c < d
        assert max(a, c) <= min(b, d);
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
            assert min(b, d) <= max(a, c);
            assert min(b, d) - max(a, c) <= 0;
        }
    }
}
// </vc-code>

