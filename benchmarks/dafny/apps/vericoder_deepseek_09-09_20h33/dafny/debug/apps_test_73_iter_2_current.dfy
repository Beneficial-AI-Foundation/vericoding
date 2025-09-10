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
{
    computePosition(result, v0, v1, a, l) >= c &&
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
        assert prev <= curr;
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
    var total := 0;
    var readYesterday := 0;
    
    computePosition_nonnegative(0, v0, v1, a, l);
    
    while total < c
        invariant 1 <= days
        invariant total >= 0
        invariant total == computePosition(days - 1, v0, v1, a, l)
        decreases c - total
    {
        computePosition_nonnegative(days - 1, v0, v1, a, l);
        
        var reread := if total > l then l else total;
        var readToday := if v1 < v0 + a * (days - 1) then v1 else v0 + a * (days - 1);
        
        total := total - reread + readToday;
        readYesterday := readToday;
        days := days + 1;
        
        computePosition_nonnegative(days - 1, v0, v1, a, l);
    }
    
    result := days - 1;
    
    assert computePosition(result, v0, v1, a, l) >= c;
    computePosition_monotonic(result, v0, v1, a, l);
    
    assert forall d :: 1 <= d < result ==> computePosition(d, v0, v1, a, l) < c;
}
// </vc-code>

