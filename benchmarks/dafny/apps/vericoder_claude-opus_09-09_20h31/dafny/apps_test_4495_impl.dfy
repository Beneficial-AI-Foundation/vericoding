predicate ValidInput(a: int, b: int, x: int)
{
    a >= 0 && b >= a && x > 0
}

function CountDivisibleInRange(a: int, b: int, x: int): int
    requires ValidInput(a, b, x)
    ensures CountDivisibleInRange(a, b, x) >= 0
{
    if a == 0 then
        b / x + 1
    else
        b / x - (a - 1) / x
}

// <vc-helpers>
lemma DivisionMonotonic(p: int, q: int, x: int)
    requires x > 0
    requires p <= q
    requires p >= 0
    ensures p / x <= q / x
{
    // For non-negative integers, if p <= q, then p/x <= q/x
    // This follows from the definition of integer division
    // Dafny can verify this automatically with the given preconditions
}

lemma CountDivisibleNonNegative(a: int, b: int, x: int)
    requires ValidInput(a, b, x)
    ensures if a == 0 then b / x + 1 >= 0 else b / x - (a - 1) / x >= 0
{
    if a == 0 {
        assert b >= 0;
        assert x > 0;
        assert b / x >= 0;
        assert b / x + 1 >= 0;
    } else {
        assert a >= 1;
        assert a - 1 >= 0;
        assert b >= a;
        assert b >= a - 1;
        DivisionMonotonic(a - 1, b, x);
        assert (a - 1) / x <= b / x;
        assert b / x - (a - 1) / x >= 0;
    }
}

lemma VerifyCountDivisibleInRange(a: int, b: int, x: int)
    requires ValidInput(a, b, x)
    ensures CountDivisibleInRange(a, b, x) >= 0
{
    CountDivisibleNonNegative(a, b, x);
    if a == 0 {
        assert CountDivisibleInRange(a, b, x) == b / x + 1;
        assert b / x + 1 >= 0;
    } else {
        assert CountDivisibleInRange(a, b, x) == b / x - (a - 1) / x;
        assert b / x - (a - 1) / x >= 0;
    }
}
// </vc-helpers>

// <vc-spec>
method CountDivisible(a: int, b: int, x: int) returns (count: int)
    requires ValidInput(a, b, x)
    ensures count == CountDivisibleInRange(a, b, x)
    ensures count >= 0
// </vc-spec>
// <vc-code>
{
    VerifyCountDivisibleInRange(a, b, x);
    if a == 0 {
        count := b / x + 1;
    } else {
        count := b / x - (a - 1) / x;
    }
    assert count == CountDivisibleInRange(a, b, x);
}
// </vc-code>

