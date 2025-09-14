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
lemma Lemma1009Works(k: int, a: int, b: int, v: int)
    requires ValidInput(k, a, b, v)
    ensures CanStoreNuts(1009, k, a, b, v)
{
    if b <= (k-1)*1009 {
        calc {
            v * (1009 + min(b, (k-1)*1009));
            == v * (1009 + b);
            >= 1 * (1009 + b);
            >= 1 * (1009 + 1);
            == 1010;
            >= 1000;
            >= a;
        }
    } else {
        calc {
            v * (1009 + min(b, (k-1)*1009));
            == v * (1009 + (k-1)*1009);
            == v * (k * 1009);
            >= 1 * (k * 1009);
            >= 1 * (2 * 1009);
            == 2018;
            >= 1000;
            >= a;
        }
    }
}

lemma MinimalSolutionExists(k: int, a: int, b: int, v: int)
    requires ValidInput(k, a, b, v)
    ensures exists i :: 1 <= i <= 1009 && CanStoreNuts(i, k, a, b, v) && 
            (forall j :: 1 <= j < i ==> !CanStoreNuts(j, k, a, b, v))
{
    Lemma1009Works(k, a, b, v);
    var i := 1;
    while i <= 1009
        invariant 1 <= i <= 1010
        invariant forall j :: 1 <= j < i ==> !CanStoreNuts(j, k, a, b, v)
        invariant i == 1 || !CanStoreNuts(i-1, k, a, b, v)
    {
        if CanStoreNuts(i, k, a, b, v) {
            assert i == 1 || !CanStoreNuts(i-1, k, a, b, v);
            return;
        }
        i := i + 1;
    }
    assert false;
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
    MinimalSolutionExists(k, a, b, v);
    var i := 1;
    while i <= 1009
        invariant 1 <= i <= 1010
// </vc-code>

