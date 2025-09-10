function computePosition(days: int, v0: int, v1: int, a: int, l: int): int
    requires days >= 0
    requires v0 >= 0 && v1 >= v0 && a >= 0 && l >= 0
    decreases days
{
    if days == 0 then 0
    else
        var prevPos := computePosition(days - 1, v0, v1, a, l);
        var afterReread := if prevPos - l > 0 then prevPos - l else 0;
        var readToday := if v1 < v0 + a * (days - 1) then v1 else v0 + a * (days - 1);
        afterReread + readToday
}

// <vc-helpers>
lemma compute_increase(days: int, v0: int, v1: int, a: int, l: int)
    requires days >= 0
    requires 0 <= l < v0 <= v1
    requires a >= 0
    ensures computePosition(days + 1, v0, v1, a, l) >= computePosition(days, v0, v1, a, l) + 1
{
    var prev := computePosition(days, v0, v1, a, l);
    var afterReread := if prev - l > 0 then prev - l else 0;
    var readToday := if v1 < v0 + a * days then v1 else v0 + a * days;
    var next := afterReread + readToday;
    assert readToday >= v0;
    if prev >= l {
        assert afterReread == prev - l;
        // prev - l + v0 >= prev + 1 because v0 - l >= 1
        assert prev - l + v0 >= prev + 1;
        assert next >= prev - l + v0;
        assert next >= prev + 1;
    } else {
        assert afterReread == 0;
        // prev < l < v0 implies v0 >= prev + 1
        assert v0 >= prev + 1;
        assert next >= v0;
        assert next >= prev + 1;
    }
    // next is exactly computePosition(days+1,...)
    assert next == computePosition(days + 1, v0, v1, a, l);
    assert prev == computePosition(days, v0, v1, a, l);
}

lemma monotone_strict(m: int, n: int, v0: int, v1: int, a: int, l: int)
    requires 0 <= l < v0 <= v1
    requires a >= 0
    requires m >= 0 && n > m
    ensures computePosition(m, v0, v1, a, l) < computePosition(n, v0, v1, a, l)
    decreases n
{
    if n == m + 1 {
        call compute_increase(m, v0, v1, a, l);
        assert computePosition(m, v0, v1, a, l) < computePosition(n, v0, v1, a, l);
    } else {
        call monotone_strict(m, n - 1, v0, v1, a, l);
        call compute_increase(n - 1, v0, v1, a, l);
        // transitivity
        assert computePosition(m, v0, v1, a, l) < computePosition(n - 1, v0, v1, a, l);
        assert computePosition(n - 1, v0, v1, a, l) < computePosition(n, v0, v1, a, l);
        assert computePosition(m, v0, v1, a, l) < computePosition(n, v0, v1, a, l);
    }
}

lemma position_ge_n(n: int, v0: int, v1: int, a: int, l: int)
    requires n >= 0
    requires 0 <= l < v0 <= v1
    requires a >= 0
    ensures computePosition(n, v0, v1, a, l) >= n
    decreases n
{
    if n == 0 {
        assert computePosition(0, v0, v1, a, l) == 0;
    } else {
        call position_ge_n(n - 1, v0, v1, a, l);
        call compute_increase(n - 1, v0, v1, a, l);
        assert computePosition(n, v0, v1, a, l) >= computePosition(n - 1, v0, v1, a, l) + 1;
        assert computePosition(n - 1, v0, v1, a, l) >= n - 1;
        assert computePosition(n, v0, v1, a, l) >= n;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(c: int, v0: int, v1: int, a: int, l: int) returns (result: int)
    requires 1 <= c <= 1000
    requires 0 <= l < v0 <= v1 <= 1000
    requires 0 <= a <= 1000
    ensures result >= 1
    ensures computePosition(result, v0, v1, a, l) >= c
    ensures forall days :: 1 <= days < result ==> computePosition(days, v0, v1, a, l) < c
// </vc-spec>
// <vc-code>
{
    var days := 1;
    while true
        invariant 1 <= days <= c
        invariant forall k | 1 <= k < days :: computePosition(k, v0, v1, a, l) < c
        decreases c - days + 1
    {
        if computePosition(days, v0, v1, a, l) >= c {
            result := days;
            // the invariant already guarantees minimality
            assert forall d | 1 <= d < result :: computePosition(d, v0, v1, a, l) < c;
            return;
        }
        // ensure days < c so that days + 1 <= c holds and the invariant is preserved
        call position_ge_n(days, v0, v1, a, l);
        assert computePosition(days, v0, v1, a, l) >= days;
        assert computePosition(days, v0, v1, a, l) < c;
        assert days < c;
        days := days + 1;
    }
}
// </vc-code>

