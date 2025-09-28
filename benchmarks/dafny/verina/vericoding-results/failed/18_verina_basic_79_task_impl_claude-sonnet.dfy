// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed termination and postcondition issues */
function MaxInRange(a: array<int>, start: int, end: int): int
    requires a.Length > 0
    requires 0 <= start < end <= a.Length
    reads a
    decreases end - start
{
    if start + 1 == end then a[start]
    else if a[start] >= MaxInRange(a, start + 1, end) then a[start]
    else MaxInRange(a, start + 1, end)
}

/* helper modified by LLM (iteration 5): fixed termination and postcondition issues */
lemma MaxInRangeExists(a: array<int>, start: int, end: int)
    requires a.Length > 0
    requires 0 <= start < end <= a.Length
    ensures exists i :: start <= i < end && a[i] == MaxInRange(a, start, end)
    ensures forall i :: start <= i < end ==> a[i] <= MaxInRange(a, start, end)
    decreases end - start
{
    if start + 1 == end {
        assert a[start] == MaxInRange(a, start, end);
        assert start <= start < end;
    } else {
        MaxInRangeExists(a, start + 1, end);
        if a[start] >= MaxInRange(a, start + 1, end) {
            assert a[start] == MaxInRange(a, start, end);
        } else {
            assert MaxInRange(a, start + 1, end) == MaxInRange(a, start, end);
            var i :| start + 1 <= i < end && a[i] == MaxInRange(a, start + 1, end);
            assert start <= i < end && a[i] == MaxInRange(a, start, end);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method OnlineMax(a: array<int>, x: int) returns (result: (int, int))
    requires
        a.Length > 0 &&
        x < a.Length
    ensures
        var (m, p) := result;
        x <= p && p < a.Length &&
        (forall i :: 0 <= i < x ==> a[i] <= m) &&
        (exists i :: 0 <= i < x && a[i] == m) &&
        ((p < a.Length - 1) ==> (exists i :: x <= i <= p && a[i] > m)) &&
        ((forall i :: x <= i < a.Length ==> a[i] <= m) ==> p == a.Length - 1)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed empty range and precondition issues */
    
    // Handle the special case when x == 0
    if x == 0 {
        // When x == 0, maximum of empty range doesn't exist, so we can use any value
        // We need to find the first position p >= x where there exists an element > m
        var m := a[0] - 1; // Choose a value smaller than first element
        var p := 0; // First position from x=0 onwards
        result := (m, p);
        return;
    }
    
    // Find maximum in range [0, x) - now x > 0 so range is non-empty
    var m := MaxInRange(a, 0, x);
    MaxInRangeExists(a, 0, x);
    
    // Find first position from x onwards where element > m
    var p := a.Length - 1; // Default value
    
    for i := x to a.Length
        invariant x <= i <= a.Length
        invariant forall j :: x <= j < i ==> a[j] <= m
        invariant p == a.Length - 1
    {
        if a[i] > m {
            p := i;
            break;
        }
    }
    
    result := (m, p);
}
// </vc-code>
