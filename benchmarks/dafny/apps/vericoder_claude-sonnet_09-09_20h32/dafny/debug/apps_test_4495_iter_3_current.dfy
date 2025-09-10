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
        assert b >= 0;
        assert b / x >= 0;
        assert 0 / x == 0;
    } else {
        var q_a := a / x;
        var r_a := a % x;
        var q_b := b / x;
        var r_b := b % x;
        
        assert a == q_a * x + r_a;
        assert b == q_b * x + r_b;
        assert 0 <= r_a < x;
        assert 0 <= r_b < x;
        
        if q_b < q_a {
            assert b == q_b * x + r_b < q_a * x <= a;
            assert false;
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
// </vc-helpers>

// <vc-spec>
method CountDivisible(a: int, b: int, x: int) returns (count: int)
    requires ValidInput(a, b, x)
    ensures count == CountDivisibleInRange(a, b, x)
    ensures count >= 0
// </vc-spec>
// <vc-code>
{
    if a == 0 {
        count := b / x + 1;
    } else {
        DivisionNonNegativity(a, b, x);
        count := b / x - (a - 1) / x;
    }
}
// </vc-code>

