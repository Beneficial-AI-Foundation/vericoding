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
function min_boxes_required(k: int, a: int, b: int, v: int): int
    requires ValidInput(k, a, b, v)
    ensures 1 <= min_boxes_required(k, a, b, v) <= 1009
    ensures CanStoreNuts(min_boxes_required(k, a, b, v), k, a, b, v)
    ensures forall i :: 1 <= i < min_boxes_required(k, a, b, v) ==> !CanStoreNuts(i, k, a, b, v)
{
    // The range for numBoxes is 1 to 1009.
    // We are looking for the smallest numBoxes such that a <= v * (numBoxes + min(b, (k - 1) * numBoxes))
    // We can iterate upwards from 1 to find the minimal solution.
    var numBoxes := 1;
    while numBoxes <= 1009
        invariant 1 <= numBoxes <= 1010
        invariant forall i :: 1 <= i < numBoxes ==> !CanStoreNuts(i, k, a, b, v)
    {
        if CanStoreNuts(numBoxes, k, a, b, v)
        {
            return numBoxes;
        }
        numBoxes := numBoxes + 1;
    }
    // This return statement should ideally not be reached if a solution always exists within the bound.
    // Based on the constraints, 1009 boxes should be sufficient.
    return 1009; // Fallback, though a solution should be found earlier.
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
    var high := 1009; // Upper bound for result based on problem constraints
    var ans := 1009; // Initialize with a value within the valid range

    // We can prove that a solution always exists within the range [1, 1009]
    // Specifically, CanStoreNuts(1009, k, a, b, v) is true under the given constraints.
    // BoxCapacity(1009, k, b, v) = v * (1009 + min(b, (k - 1) * 1009))
    // Since k >= 2, (k-1) * 1009 >= 1009.
    // Since b >= 1, min(b, (k-1)*1009) >= 1. (Actually, min(b, ...) will be at least 1)
    // BoxCapacity(1009, k, b, v) >= v * (1009 + 1) = 1010 * v.
    // Since v >= 1, BoxCapacity(1009, k, b, v) >= 1010.
    // Since a <= 1000, we have BoxCapacity(1009, k, b, v) >= a.
    // Thus, CanStoreNuts(1009, k, a, b, v) is always true.

    while low <= high
        invariant 1 <= low <= high + 1 <= 1010
        invariant 1 <= ans <= 1009
        invariant CanStoreNuts(ans, k, a, b, v)
        invariant forall i :: 1 <= i < low ==> !CanStoreNuts(i, k, a, b, v)
        invariant forall i :: high < i <= 1009 ==> CanStoreNuts(i, k, a, b, v)
        decreases high - low
    {
        var mid := low + (high - low) / 2;
        if CanStoreNuts(mid, k, a, b, v)
        {
            ans := mid;
            high := mid - 1;
        } else
        {
            low := mid + 1;
        }
    }
    result := ans;
}
// </vc-code>

