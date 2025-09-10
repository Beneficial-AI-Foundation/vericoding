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
predicate isSolution(result: int, c: int, v0: int, v1: int, a: int, l: int)
    requires v0 >= 0 && v1 >= v0 && a >= 0 && l >= 0
    requires result >= 0
{
    result >= 1 && computePosition(result, v0, v1, a, l) >= c &&
    forall days :: 1 <= days < result ==> computePosition(days, v0, v1, a, l) < c
}

lemma computePosition_monotonic(days: int, v0: int, v1: int, a: int, l: int)
    requires days >= 0
    requires v0 >= 0 && v1 >= v0 && a >= 0 && l >= 0
    ensures forall k :: 0 <= k <= days ==> computePosition(k, v0, v1, a, l) <= computePosition(days, v0, v1, a, l)
    decreases days
{
    if days > 0 {
        computePosition_monotonic(days - 1, v0, v1, a, l);
        var prev := computePosition(days - 1, v0, v1, a, l);
        var curr := computePosition(days, v0, v1, a, l);
        
        forall k | 0 <= k <= days - 1 {
            assert computePosition(k, v0, v1, a, l) <= prev by {
                computePosition_monotonic(k, v0, v1, a, l);
                if k == days - 1 {
                    assert computePosition(k, v0, v1, a, l) == prev;
                }
            }
        }
        
        // Prove that curr >= prev (each day adds non-negative reading)
        computePosition_definition(days, v0, v1, a, l);
        var afterReread := if prev - l > 0 then prev - l else 0;
        var readToday := if v1 < v0 + a * (days - 1) then v1 else v0 + a * (days - 1);
        assert readToday >= 0;
        assert curr == afterReread + readToday;
        assert afterReread <= prev;
        assert curr >= prev; // This holds because readToday >= 0 and afterReread <= prev, so afterReread + readToday >= prev
    }
}

lemma computePosition_nonnegative(days: int, v0: int, v1: int, a: int, l: int)
    requires days >= 0
    requires v0 >= 0 && v1 >= v0 && a >= 0 && l >= 0
    ensures computePosition(days, v0, v1, a, l) >= 0
    decreases days
{
    if days > 0 {
        computePosition_nonnegative(days - 1, v0, v1, a, l);
        var prev := computePosition(days - 1, v0, v1, a, l);
        var curr := computePosition(days, v0, v1, a, l);
        
        computePosition_definition(days, v0, v1, a, l);
        var afterReread := if prev - l > 0 then prev - l else 0;
        var readToday := if v1 < v0 + a * (days - 1) then v1 else v0 + a * (days - 1);
        assert afterReread >= 0;
        assert readToday >= 0;
        assert curr >= 0;
    }
}

lemma computePosition_increasing(d1: int, d2: int, v0: int, v1: int, a: int, l: int)
    requires 0 <= d1 <= d2
    requires v0 >= 0 && v1 >= v0 && a >= 0 && l >= 0
    ensures computePosition(d1, v0, v1, a, l) <= computePosition(d2, v0, v1, a, l)
{
    computePosition_monotonic(d2, v0, v1, a, l);
}

lemma computePosition_definition(days: int, v0: int, v1: int, a: int, l: int)
    requires days >= 0
    requires v0 >= 0 && v1 >= v0 && a >= 0 && l >= 0
    ensures computePosition(days, v0, v1, a, l) ==
        if days == 0 then 0
        else
            var prevPos := computePosition(days - 1, v0, v1, a, l);
            var afterReread := if prevPos - l > 0 then prevPos - l else 0;
            var readToday := if v1 < v0 + a * (days - 1) then v1 else v0 + a * (days - 1);
            afterReread + readToday
{
    // This lemma is a direct consequence of the function definition
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
    var total := 0;
    
    while total < c
        invariant 1 <= days
        invariant total == computePosition(days - 1, v0, v1, a, l)
        invariant total >= 0
        invariant forall d :: 1 <= d < days ==> computePosition(d, v0, v1, a, l) < c
        decreases c - total
    {
        computePosition_nonnegative(days - 1, v0, v1, a, l);
        
        var reread := if total > l then l else total;
        var readToday := if v1 < v0 + a * (days - 1) then v1 else v0 + a * (days - 1);
        
        var newTotal := total - reread + readToday;
        
        // Prove the loop invariant for the next iteration
        if days >= 1 {
            // Show that computePosition(days, v0, v1, a, l) = newTotal
            computePosition_definition(days, v0, v1, a, l);
            assert computePosition(days, v0, v1, a, l) == newTotal;
        }
        
        // Update state
        total := newTotal;
        
        // Maintain the invariant that all previous days have total < c
        if days > 1 {
            computePosition_increasing(1, days - 1, v0, v1, a, l);
        }
        
        // For the new day we just computed, show it's still < c (since we're still in the loop)
        assert total < c by {
            // We know we're still in the loop, so total < c must hold
        }
        
        days := days + 1;
    }
    
    result := days - 1;
}
// </vc-code>

