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
lemma ExistenceLemma(k: int, a: int, b: int, v: int)
    requires ValidInput(k, a, b, v)
    ensures CanStoreNuts(1009, k, a, b, v)
{
    // b >= 1
    assert b >= 1;
    // (k-1) >= 1 for k >= 2, so (k-1)*1009 >= 1009
    assert (k - 1) * 1009 >= 1009;
    // min(b, (k-1)*1009) >= 1
    assert min(b, (k - 1) * 1009) >= 1;
    // BoxCapacity(1009, ...) = v * (1009 + min(...)) >= v*(1009+1)
    assert BoxCapacity(1009, k, b, v) >= v * (1009 + 1);
    // v >= 1
    assert v >= 1;
    // hence BoxCapacity(1009, ...) >= 1010 >= a (since a <= 1000)
    assert BoxCapacity(1009, k, b, v) >= 1010;
    assert BoxCapacity(1009, k, b, v) >= a;
}

method FindMinimal(k: int, a: int, b: int, v: int) returns (i: int)
    requires ValidInput(k, a, b, v)
    ensures 1 <= i <= 1009
    ensures IsMinimalSolution(i, k, a, b, v)
    ensures forall h :: 1 <= h < i ==> !CanStoreNuts(h, k, a, b, v)
{
    ExistenceLemma(k, a, b, v);
    var j := 1;
    while !CanStoreNuts(j, k, a, b, v)
        invariant 1 <= j <= 1009
        invariant forall h :: 1 <= h < j ==> !CanStoreNuts(h, k, a, b, v)
        decreases 1009 - j
    {
        j := j + 1;
    }
    i := j;
    // i satisfies CanStoreNuts by loop exit
    assert CanStoreNuts(i, k, a, b, v);
    // minimality follows from invariant
    if i > 1 {
        assert forall h :: 1 <= h < i ==> !CanStoreNuts(h, k, a, b, v);
    }
}

method ExistenceOfSolutionViaFindMinimal(k: int, a: int, b: int, v: int)
    requires ValidInput(k, a, b, v)
    ensures exists i :: 1 <= i <= 1009 && CanStoreNuts(i, k, a, b, v) && (forall j :: 1 <= j < i ==> !CanStoreNuts(j, k, a, b, v))
{
    var r := FindMinimal(k, a, b, v);
    assert 1 <= r <= 1009;
    assert CanStoreNuts(r, k, a, b, v);
    assert forall j :: 1 <= j < r ==> !CanStoreNuts(j, k, a, b, v);
    // witness r
    assert exists i :: 1 <= i <= 1009 && CanStoreNuts(i, k, a, b, v) && (forall j :: 1 <= j < i ==> !CanStoreNuts(j, k, a, b, v)) by {
        reveal; // help solver with the trivial witness
    };
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
    result := FindMinimal(k, a, b, v);
    // Re-establish the postconditions explicitly for the verifier.
    assert 1 <= result <= 1009;
    assert CanStoreNuts(result, k, a, b, v);
    assert forall j :: 1 <= j < result ==> !CanStoreNuts(j, k, a, b, v);
    // Provide the required existential witness
    assert exists i :: 1 <= i <= 1009 && CanStoreNuts(i, k, a, b, v) && result == i && (forall j :: 1 <= j < i ==> !CanStoreNuts(j, k, a, b, v));
}
// </vc-code>

