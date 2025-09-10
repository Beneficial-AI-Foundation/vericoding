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
lemma BoxCapacityMonotonic(n1: int, n2: int, k: int, b: int, v: int)
    requires n1 >= 0 && n2 >= n1
    requires k >= 2 && b >= 1 && v >= 1
    ensures BoxCapacity(n1, k, b, v) <= BoxCapacity(n2, k, b, v)
{
    // Since n2 >= n1, we have n2 >= n1
    assert n2 >= n1;
    
    // For the min terms: min(b, (k-1)*n2) >= min(b, (k-1)*n1) since n2 >= n1
    if (k - 1) * n1 >= b {
        // min(b, (k-1)*n1) = b
        // Since n2 >= n1, we have (k-1)*n2 >= (k-1)*n1 >= b
        // So min(b, (k-1)*n2) = b
        assert min(b, (k - 1) * n1) == b;
        assert min(b, (k - 1) * n2) == b;
    } else {
        // min(b, (k-1)*n1) = (k-1)*n1
        // min(b, (k-1)*n2) >= (k-1)*n1 since n2 >= n1
        assert min(b, (k - 1) * n1) == (k - 1) * n1;
        assert min(b, (k - 1) * n2) >= (k - 1) * n2;
        assert (k - 1) * n2 >= (k - 1) * n1;
    }
    
    // Both n2 >= n1 and min(b, (k-1)*n2) >= min(b, (k-1)*n1)
    // So n2 + min(b, (k-1)*n2) >= n1 + min(b, (k-1)*n1)
    // Multiplying by v >= 1 preserves the inequality
}

lemma CanStoreNutsMonotonic(n1: int, n2: int, k: int, a: int, b: int, v: int)
    requires n1 >= 0 && n2 >= n1
    requires k >= 2 && b >= 1 && v >= 1
    requires CanStoreNuts(n2, k, a, b, v)
    ensures CanStoreNuts(n1, k, a, b, v) || n1 == 0
{
    if n1 > 0 {
        BoxCapacityMonotonic(n1, n2, k, b, v);
    }
}

lemma EventuallyCanStore(k: int, a: int, b: int, v: int)
    requires ValidInput(k, a, b, v)
    ensures CanStoreNuts(1009, k, a, b, v)
{
    assert BoxCapacity(1009, k, b, v) >= v * 1009;
    assert v * 1009 >= 1000;
    assert a <= 1000;
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
    result := 1;
    
    while result <= 1009 && !CanStoreNuts(result, k, a, b, v)
        invariant 1 <= result <= 1010
        invariant forall j :: 1 <= j < result ==> !CanStoreNuts(j, k, a, b, v)
        decreases 1010 - result
    {
        result := result + 1;
    }
    
    EventuallyCanStore(k, a, b, v);
    
    assert result <= 1009;
    assert CanStoreNuts(result, k, a, b, v);
    assert forall j :: 1 <= j < result ==> !CanStoreNuts(j, k, a, b, v);
}
// </vc-code>

