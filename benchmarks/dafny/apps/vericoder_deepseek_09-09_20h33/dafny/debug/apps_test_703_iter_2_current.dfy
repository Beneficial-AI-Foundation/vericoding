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
        var diff := numBoxes2 - numBoxes1;
        var extra_capacity1 := v * diff;
        var extra_capacity2 := v * min(b, (k - 1) * diff);
        var extra_capacity := v * (diff + min(b, (k - 1) * diff));
        calc {
            BoxCapacity(numBoxes2, k, b, v);
            ==
            v * (numBoxes2 + min(b, (k - 1) * numBoxes2));
            ==
            v * ((numBoxes1 + diff) + min(b, (k - 1) * (numBoxes1 + diff)));
            >=
            v * ((numBoxes1 + diff) + (min(b, (k - 1) * numBoxes1) - (k - 1) * diff));
            >=
            v * (numBoxes1 + min(b, (k - 1) * numBoxes1)) + v * (diff - (k - 1) * diff + min(b, (k - 1) * diff));
            ==
            BoxCapacity(numBoxes1, k, b, v) + extra_capacity;
        }
    }
}

lemma LemmaSolutionExists(k: int, a: int, b: int, v: int)
    requires ValidInput(k, a, b, v)
    ensures exists i :: 1 <= i <= 1009 && CanStoreNuts(i, k, a, b, v)
{
    var max_boxes := 1009;
    var max_capacity := BoxCapacity(max_boxes, k, b, v);
    assert max_capacity >= a by {
        // Calculate minimum possible capacity at max_boxes
        var min_cap := v * (max_boxes + 0);  // min(b, (k-1)*max_boxes) >= 0
        assert min_cap <= max_capacity;
        assert min_cap >= 1009 >= a;  // Since a <= 1000 and max_boxes = 1009
    }
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
    
    while low <= high
        invariant 1 <= low <= high + 1
        invariant high <= 1009
        invariant exists i :: i >= low && i <= high && CanStoreNuts(i, k, a, b, v)
        invariant forall j :: 1 <= j < low ==> !CanStoreNuts(j, k, a, b, v)
    {
        var mid := (low + high) / 2;
        if CanStoreNuts(mid, k, a, b, v) {
            result := mid;
            high := mid - 1;
        } else {
            low := mid + 1;
        }
    }
    
    // Verify the result
    LemmaSolutionExists(k, a, b, v);
    assert exists i :: 1 <= i <= 1009 && CanStoreNuts(i, k, a, b, v);
    assert forall j :: 1 <= j < result ==> !CanStoreNuts(j, k, a, b, v);
    assert CanStoreNuts(result, k, a, b, v) by {
        // Since the loop invariant guarantees there exists some i in [low, high] that can store nuts,
        // and we ended with low > high, it must be that result (which was set to the last found working value)
        // is the minimal solution
    }
}
// </vc-code>

