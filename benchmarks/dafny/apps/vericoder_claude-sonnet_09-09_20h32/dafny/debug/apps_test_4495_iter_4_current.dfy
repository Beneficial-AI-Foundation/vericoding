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
lemma DivisionMonotonicity(a: int, b: int, x: int)
    requires a >= 0 && b >= a && x > 0
    ensures b / x >= a / x
{
    if a == 0 {
        assert b / x >= 0 == 0 / x;
    } else {
        assert b >= a > 0;
        assert (b - a) >= 0;
        assert b / x >= a / x by {
            if a / x == b / x {
                assert b / x >= a / x;
            } else {
                var diff := b - a;
                assert diff >= 0;
                assert b == a + diff;
                assert b / x >= a / x;
            }
        }
    }
}

lemma DivisionNonNegativity(a: int, b: int, x: int)
    requires a >= 1 && b >= a && x > 0
    ensures b / x - (a - 1) / x >= 0
{
    DivisionMonotonicity(a - 1, b, x);
    assert b / x >= (a - 1) / x;
}

lemma CountDivisibleNonNegative(a: int, b: int, x: int)
    requires ValidInput(a, b, x)
    ensures CountDivisibleInRange(a, b, x) >= 0
{
    if a == 0 {
        assert b >= 0;
        assert b / x >= 0;
        assert CountDivisibleInRange(a, b, x) == b / x + 1 >= 1;
    } else {
        assert a >= 1;
        DivisionNonNegativity(a, b, x);
        assert b / x - (a - 1) / x >= 0;
        assert CountDivisibleInRange(a, b, x) == b / x - (a - 1) / x >= 0;
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
    CountDivisibleNonNegative(a, b, x);
    if a == 0 {
        count := b / x + 1;
    } else {
        DivisionNonNegativity(a, b, x);
        count := b / x - (a - 1) / x;
    }
}
// </vc-code>

