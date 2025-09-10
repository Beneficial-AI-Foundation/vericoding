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
lemma computePositionMonotonic(days1: int, days2: int, v0: int, v1: int, a: int, l: int)
    requires days1 >= 0 && days2 >= 0
    requires v0 >= 0 && v1 >= v0 && a >= 0 && l >= 0
    requires days1 <= days2
    ensures computePosition(days1, v0, v1, a, l) <= computePosition(days2, v0, v1, a, l)
    decreases days2
{
    if days1 == days2 {
        // trivial
    } else if days2 == 0 {
        // impossible since days1 <= days2 and days1 >= 0
    } else {
        if days1 == 0 {
            assert computePosition(days1, v0, v1, a, l) == 0;
            assert computePosition(days2, v0, v1, a, l) >= 0;
        } else {
            computePositionMonotonic(days1 - 1, days2 - 1, v0, v1, a, l);
        }
    }
}

lemma computePositionPositive(days: int, v0: int, v1: int, a: int, l: int)
    requires days >= 0
    requires v0 >= 0 && v1 >= v0 && a >= 0 && l >= 0
    ensures computePosition(days, v0, v1, a, l) >= 0
    decreases days
{
    if days == 0 {
        // trivial
    } else {
        computePositionPositive(days - 1, v0, v1, a, l);
    }
}

lemma computePositionBound(days: int, v0: int, v1: int, a: int, l: int)
    requires days >= 0
    requires v0 >= 0 && v1 >= v0 && a >= 0 && l >= 0
    ensures computePosition(days, v0, v1, a, l) <= days * v1
{
    var d := 0;
    while d < days
        invariant 0 <= d <= days
        invariant computePosition(d, v0, v1, a, l) <= d * v1
    {
        d := d + 1;
        var prevPos := computePosition(d - 1, v0, v1, a, l);
        var afterReread := if prevPos - l > 0 then prevPos - l else 0;
        var readToday := if v1 < v0 + a * (d - 1) then v1 else v0 + a * (d - 1);
        assert readToday <= v1;
        assert computePosition(d, v0, v1, a, l) == afterReread + readToday;
        assert afterReread <= prevPos;
        assert prevPos <= (d - 1) * v1;
        assert afterReread + readToday <= (d - 1) * v1 + v1;
        assert afterReread + readToday <= d * v1;
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
    var candidate := 1;
    
    while computePosition(candidate, v0, v1, a, l) < c
        invariant candidate >= 1
        invariant forall days :: 1 <= days < candidate ==> computePosition(days, v0, v1, a, l) < c
        decreases c - computePosition(candidate, v0, v1, a, l)
    {
        computePositionMonotonic(candidate, candidate + 1, v0, v1, a, l);
        computePositionBound(candidate + 1, v0, v1, a, l);
        candidate := candidate + 1;
    }
    
    result := candidate;
}
// </vc-code>

