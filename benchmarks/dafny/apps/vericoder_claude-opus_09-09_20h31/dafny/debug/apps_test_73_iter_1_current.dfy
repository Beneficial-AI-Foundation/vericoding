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
lemma computePositionIncreasing(days: int, v0: int, v1: int, a: int, l: int)
    requires days >= 0
    requires v0 >= 0 && v1 >= v0 && a >= 0 && l >= 0
    ensures days > 0 ==> computePosition(days, v0, v1, a, l) >= computePosition(days - 1, v0, v1, a, l) - l + v0
    decreases days
{
    if days <= 0 {
        // Base case
    } else {
        var prevPos := computePosition(days - 1, v0, v1, a, l);
        var afterReread := if prevPos - l > 0 then prevPos - l else 0;
        var readToday := if v1 < v0 + a * (days - 1) then v1 else v0 + a * (days - 1);
        
        assert readToday >= v0;
        assert computePosition(days, v0, v1, a, l) == afterReread + readToday;
        
        if prevPos - l > 0 {
            assert afterReread == prevPos - l;
            assert computePosition(days, v0, v1, a, l) == prevPos - l + readToday;
            assert computePosition(days, v0, v1, a, l) >= prevPos - l + v0;
        } else {
            assert afterReread == 0;
            assert computePosition(days, v0, v1, a, l) == readToday;
            assert computePosition(days, v0, v1, a, l) >= v0;
            assert computePosition(days, v0, v1, a, l) >= prevPos - l + v0;
        }
    }
}

lemma computePositionMonotonic(days1: int, days2: int, v0: int, v1: int, a: int, l: int)
    requires 0 <= days1 <= days2
    requires v0 > l
    requires v0 >= 0 && v1 >= v0 && a >= 0 && l >= 0
    ensures computePosition(days1, v0, v1, a, l) <= computePosition(days2, v0, v1, a, l)
    decreases days2 - days1
{
    if days1 == days2 {
        // Base case: equal days means equal positions
    } else {
        // Inductive step
        computePositionMonotonic(days1, days2 - 1, v0, v1, a, l);
        computePositionIncreasing(days2, v0, v1, a, l);
        
        var prevPos := computePosition(days2 - 1, v0, v1, a, l);
        var afterReread := if prevPos - l > 0 then prevPos - l else 0;
        var readToday := if v1 < v0 + a * (days2 - 1) then v1 else v0 + a * (days2 - 1);
        
        assert readToday >= v0;
        assert v0 > l;
        
        if prevPos - l > 0 {
            assert computePosition(days2, v0, v1, a, l) == prevPos - l + readToday;
            assert computePosition(days2, v0, v1, a, l) >= prevPos - l + v0;
            assert computePosition(days2, v0, v1, a, l) > prevPos;
        } else {
            assert computePosition(days2, v0, v1, a, l) == readToday;
            assert computePosition(days2, v0, v1, a, l) >= v0;
            assert v0 > l >= prevPos;
            assert computePosition(days2, v0, v1, a, l) > prevPos;
        }
        
        assert computePosition(days2, v0, v1, a, l) > computePosition(days2 - 1, v0, v1, a, l);
        assert computePosition(days1, v0, v1, a, l) <= computePosition(days2 - 1, v0, v1, a, l);
        assert computePosition(days1, v0, v1, a, l) < computePosition(days2, v0, v1, a, l);
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
    
    while computePosition(days, v0, v1, a, l) < c
        invariant days >= 1
        invariant forall d :: 1 <= d < days ==> computePosition(d, v0, v1, a, l) < c
        decreases c - computePosition(days, v0, v1, a, l)
    {
        days := days + 1;
        
        if days > c {
            // Upper bound: if we read v0 pages every day (minimum), after c days we'd have read at least c pages
            // even with forgetting l < v0 pages each night
            assert v0 > l;
            computePositionMonotonic(c, days, v0, v1, a, l);
            assert computePosition(days, v0, v1, a, l) >= computePosition(c, v0, v1, a, l);
            
            // After c days, we've read at least c pages (since v0 > l, we make progress)
            var minProgress := v0 - l;
            assert minProgress > 0;
            assert computePosition(c, v0, v1, a, l) >= c;
            assert computePosition(days, v0, v1, a, l) >= c;
            assert false;
        }
    }
    
    result := days;
}
// </vc-code>

