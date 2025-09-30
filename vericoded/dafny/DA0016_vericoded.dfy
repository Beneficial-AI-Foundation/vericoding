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

lemma computePositionLowerBound(days: int, v0: int, v1: int, a: int, l: int)
    requires days >= 0
    requires v0 > l
    requires v0 >= 0 && v1 >= v0 && a >= 0 && l >= 0
    ensures computePosition(days, v0, v1, a, l) >= days * (v0 - l)
    decreases days
{
    if days == 0 {
        assert computePosition(0, v0, v1, a, l) == 0;
        assert 0 >= 0 * (v0 - l);
    } else {
        computePositionLowerBound(days - 1, v0, v1, a, l);
        var prevPos := computePosition(days - 1, v0, v1, a, l);
        var afterReread := if prevPos - l > 0 then prevPos - l else 0;
        var readToday := if v1 < v0 + a * (days - 1) then v1 else v0 + a * (days - 1);
        
        assert prevPos >= (days - 1) * (v0 - l);
        assert readToday >= v0;
        
        if prevPos - l > 0 {
            assert afterReread == prevPos - l;
            assert afterReread >= (days - 1) * (v0 - l) - l;
            assert computePosition(days, v0, v1, a, l) == afterReread + readToday;
            assert computePosition(days, v0, v1, a, l) >= (days - 1) * (v0 - l) - l + v0;
            assert computePosition(days, v0, v1, a, l) >= days * (v0 - l);
        } else {
            assert afterReread == 0;
            assert prevPos <= l;
            assert computePosition(days, v0, v1, a, l) == readToday;
            assert computePosition(days, v0, v1, a, l) >= v0;
            
            // Since prevPos <= l and prevPos >= (days-1)*(v0-l), we have (days-1)*(v0-l) <= l
            // This means days <= l/(v0-l) + 1
            // For small days, we can still show the bound holds
            if days == 1 {
                assert computePosition(days, v0, v1, a, l) >= v0;
                assert v0 >= 1 * (v0 - l);
                assert computePosition(days, v0, v1, a, l) >= days * (v0 - l);
            } else {
                // This case shouldn't happen for large days since we make net progress
                assert prevPos >= (days - 1) * (v0 - l);
                assert (days - 1) * (v0 - l) <= l;
                assert days * (v0 - l) <= l + (v0 - l);
                assert days * (v0 - l) <= v0;
                assert computePosition(days, v0, v1, a, l) >= v0;
                assert computePosition(days, v0, v1, a, l) >= days * (v0 - l);
            }
        }
    }
}

lemma computePositionBound(days: int, v0: int, v1: int, a: int, l: int, c: int)
    requires days >= c
    requires v0 > l
    requires c >= 1
    requires v0 >= 0 && v1 >= v0 && a >= 0 && l >= 0
    ensures computePosition(days, v0, v1, a, l) >= c
{
    computePositionLowerBound(days, v0, v1, a, l);
    assert computePosition(days, v0, v1, a, l) >= days * (v0 - l);
    assert v0 - l >= 1;
    assert computePosition(days, v0, v1, a, l) >= days;
    assert computePosition(days, v0, v1, a, l) >= c;
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
    var maxDays := c + 1;  // Upper bound on number of days needed
    
    while days <= maxDays && computePosition(days, v0, v1, a, l) < c
        invariant 1 <= days <= maxDays + 1
        invariant forall d :: 1 <= d < days ==> computePosition(d, v0, v1, a, l) < c
        decreases maxDays - days
    {
        days := days + 1;
    }
    
    if days > maxDays {
        // This case should not happen
        computePositionBound(maxDays, v0, v1, a, l, c);
        assert computePosition(maxDays, v0, v1, a, l) >= c;
        assert false;
    }
    
    assert computePosition(days, v0, v1, a, l) >= c;
    result := days;
}
// </vc-code>

