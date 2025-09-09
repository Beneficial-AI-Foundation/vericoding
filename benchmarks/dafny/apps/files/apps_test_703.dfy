Store `a` nuts in boxes using `b` available divisors. Each box can have at most `k` sections.
A box with `x` divisors has `x+1` sections. Each section holds at most `v` nuts.
Find minimum number of boxes needed.

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

method solve(k: int, a: int, b: int, v: int) returns (result: int)
    requires ValidInput(k, a, b, v)
    ensures result >= 1
    ensures result <= 1009
    ensures IsMinimalSolution(result, k, a, b, v)
    ensures exists i :: 1 <= i <= 1009 && CanStoreNuts(i, k, a, b, v) && result == i && 
            (forall j :: 1 <= j < i ==> !CanStoreNuts(j, k, a, b, v))
{
    for i := 1 to 1010 
        invariant 1 <= i <= 1010
        invariant forall j :: 1 <= j < i ==> !CanStoreNuts(j, k, a, b, v)
    {
        if CanStoreNuts(i, k, a, b, v) {
            assert CanStoreNuts(i, k, a, b, v);
            assert forall j :: 1 <= j < i ==> !CanStoreNuts(j, k, a, b, v);
            assert i == 1 || !CanStoreNuts(i - 1, k, a, b, v);
            return i;
        }
    }
    return 1009;
}
