function min(x: int, y: int): int
{
    if x <= y then x else y
}

predicate ValidInput(k: int, a: int, b: int, v: int)
{
    2 <= k <= 1000 && 1 <= a <= 1000 && 1 <= b <= 1000 && 1 <= v <= 1000
}

function BoxCapacity(numBoxes: int, k: int, b: int, v: int): int
    requires numBoxes >= 0
{
    v * (numBoxes + min(b, (k - 1) * numBoxes))
}

predicate CanStoreNuts(numBoxes: int, k: int, a: int, b: int, v: int)
    requires numBoxes >= 0
{
    a <= BoxCapacity(numBoxes, k, b, v)
}

predicate IsMinimalSolution(result: int, k: int, a: int, b: int, v: int)
    requires result >= 1
{
    CanStoreNuts(result, k, a, b, v) &&
    (result == 1 || !CanStoreNuts(result - 1, k, a, b, v))
}

// <vc-helpers>
lemma LemmaBoxCapacityMonotonic(numBoxes1: int, numBoxes2: int, k: int, b: int, v: int)
    requires numBoxes1 >= 0 && numBoxes2 >= 0
    requires numBoxes1 <= numBoxes2
    ensures BoxCapacity(numBoxes1, k, b, v) <= BoxCapacity(numBoxes2, k, b, v)
{
    if numBoxes1 < numBoxes2 {
        var cap1 := BoxCapacity(numBoxes1, k, b, v);
        var cap2 := BoxCapacity(numBoxes2, k, b, v);
        
        // min is monotonic with respect to its arguments
        assert min(b, (k - 1) * numBoxes1) <= min(b, (k - 1) * numBoxes2);
        // Both components are non-decreasing
        assert numBoxes1 + min(b, (k - 1) * numBoxes1) <= numBoxes2 + min(b, (k - 1) * numBoxes2);
    }
}

lemma LemmaSolutionExists(k: int, a: int, b: int, v: int)
    requires ValidInput(k, a, b, v)
    ensures exists i :: 1 <= i <= 1009 && CanStoreNuts(i, k, a, b, v)
{
    var max_boxes := 1009;
    var max_capacity := BoxCapacity(max_boxes, k, b, v);
    // Calculate minimum possible capacity for max boxes
    var min_cap := v * max_boxes;
    assert min_cap == v * 1009;
    assert min_cap >= 1009;  // since v >= 1
    assert a <= 1000 <= 1009 <= min_cap;
    assert CanStoreNuts(max_boxes, k, a, b, v);
}

lemma LemmaMinimalSolutionProperty(result: int, k: int, a: int, b: int, v: int)
    requires result >= 1
    requires CanStoreNuts(result, k, a, b, v)
    requires forall j :: 1 <= j < result ==> !CanStoreNuts(j, k, a, b, v)
    ensures IsMinimalSolution(result, k, a, b, v)
{
}
// </vc-helpers>

// <vc-spec>
method solve(k: int, a: int, b: int, v: int) returns (result: int)
    requires ValidInput(k, a, b, v)
    ensures result >= 1
    ensures result <= 1009
    ensures IsMinimalSolution(result, k, a, b, v)
    ensures exists i :: 1 <= i <= 1009 && CanStoreNuts(i, k, a, b, v) && result == i && 
            (forall j :: 1 <= j < i ==> !CanStoreNuts(j, k, a, b, v))
// </vc-spec>
// <vc-code>
{
    var low := 1;
    var high := 1009;
    result := high;
    
    // Prove that high can store nuts
    assert CanStoreNuts(high, k, a, b, v) by {
        var cap := BoxCapacity(high, k, b, v);
        assert cap >= v * high;
        assert v * high >= 1009;
        assert a <= 1000 <= 1009 <= v * high;
    }
    
    // Store the invariant that solutions exist in [1, 1009]
    var solution_exists := LemmaSolutionExists(k, a, b, v);
    
    while low <= high
        invariant 1 <= low <= high + 1
        invariant high <= 1009
        invariant exists i :: low <= i <= high && CanStoreNuts(i, k, a, b, v)
        invariant forall j :: 1 <= j < low ==> !CanStoreNuts(j, k, a, b, v)
        decreases high - low
    {
        var mid := (low + high) / 2;
        if CanStoreNuts(mid, k, a, b, v) {
            result := mid;
            high := mid - 1;
            // Update the "forall" invariant: now we know nothing below mid+1 works
            assert forall j :: 1 <= j < mid + 1 ==> !CanStoreNuts(j, k, a, b, v) by {
                // For j < low: already covered by invariant
                // For low <= j < mid: we need to show they don't work
                // Since mid works and boxes are monotonic, anything less than mid should work
                // But wait: boxes are NOT necessarily monotonic in the predicate CanStoreNuts?
                // Actually they are: LemmaBoxCapacityMonotonic shows that
                if low <= j < mid {
                    if CanStoreNuts(j, k, a, b, v) {
                        // This contradicts the minimality - if j works and j < mid works,
                        // then mid wouldn't be the binary search candidate
                    }
                }
            }
        } else {
            low := mid + 1;
            // Update exists invariant: the solution must be in [mid+1, high] since mid doesn't work
            // and solutions are monotonic (larger boxes have larger capacity)
            assert exists i :: low <= i <= high && CanStoreNuts(i, k, a, b, v) by {
                // The original invariant says there's a solution in [old_low, old_high]
                // Since mid doesn't work, the solution must be > mid, so >= mid+1
            }
        }
    }
    
    assert low == high + 1;
    // The result is the minimal solution
    assert CanStoreNuts(result, k, a, b, v);
    assert forall j :: 1 <= j < result ==> !CanStoreNuts(j, k, a, b, v) by {
        // From the invariant, nothing below low = result + 1 works
        // Since result <= low - 1 and j < result means j < low
    }
}
// </vc-code>

