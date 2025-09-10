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
lemma CapacityMonotonic(n1: int, n2: int, k: int, b: int, v: int)
    requires 0 <= n1 <= n2
    requires k >= 2 && b >= 1 && v >= 1
    ensures BoxCapacity(n1, k, b, v) <= BoxCapacity(n2, k, b, v)
{
    var cap1 := BoxCapacity(n1, k, b, v);
    var cap2 := BoxCapacity(n2, k, b, v);
    
    assert cap1 == v * (n1 + min(b, (k - 1) * n1));
    assert cap2 == v * (n2 + min(b, (k - 1) * n2));
    
    if (k - 1) * n1 <= b && (k - 1) * n2 <= b {
        assert min(b, (k - 1) * n1) == (k - 1) * n1;
        assert min(b, (k - 1) * n2) == (k - 1) * n2;
        assert cap1 == v * (n1 + (k - 1) * n1) == v * k * n1;
        assert cap2 == v * (n2 + (k - 1) * n2) == v * k * n2;
    } else if (k - 1) * n1 >= b && (k - 1) * n2 >= b {
        assert min(b, (k - 1) * n1) == b;
        assert min(b, (k - 1) * n2) == b;
        assert cap1 == v * (n1 + b);
        assert cap2 == v * (n2 + b);
    } else {
        assert (k - 1) * n1 <= b && (k - 1) * n2 >= b;
        assert min(b, (k - 1) * n1) == (k - 1) * n1;
        assert min(b, (k - 1) * n2) == b;
        assert cap1 == v * k * n1;
        assert cap2 == v * (n2 + b);
    }
}

lemma UpperBoundExists(k: int, a: int, b: int, v: int)
    requires ValidInput(k, a, b, v)
    ensures exists i :: 1 <= i <= 1009 && CanStoreNuts(i, k, a, b, v)
{
    var maxCapacity := BoxCapacity(1009, k, b, v);
    assert maxCapacity == v * (1009 + min(b, (k - 1) * 1009));
    
    if (k - 1) * 1009 <= b {
        assert min(b, (k - 1) * 1009) == (k - 1) * 1009;
        assert maxCapacity == v * k * 1009;
        assert k >= 2 && v >= 1;
        assert maxCapacity >= 2 * 1009 >= 2018;
    } else {
        assert min(b, (k - 1) * 1009) == b;
        assert maxCapacity == v * (1009 + b);
        assert b >= 1 && v >= 1;
        assert maxCapacity >= 1009 + 1 >= 1010;
    }
    
    assert a <= 1000;
    assert maxCapacity >= 1010 > a;
    assert CanStoreNuts(1009, k, a, b, v);
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
    
    if result > 1009 {
        UpperBoundExists(k, a, b, v);
        assert false;
    }
    
    assert CanStoreNuts(result, k, a, b, v);
    assert forall j :: 1 <= j < result ==> !CanStoreNuts(j, k, a, b, v);
    
    if result > 1 {
        assert !CanStoreNuts(result - 1, k, a, b, v);
    }
    
    assert IsMinimalSolution(result, k, a, b, v);
}
// </vc-code>

