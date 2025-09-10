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
lemma CountDivisibleInRangeLemma(a: int, b: int, x: int)
    requires ValidInput(a, b, x)
    ensures CountDivisibleInRange(a, b, x) == (b / x) - ((a - 1) / x)
{
    // This lemma establishes the relationship between the two cases
    if a == 0 {
        assert (-1) / x == -1;  // Since x > 0, -1/x = -1
        assert b / x + 1 == b / x - (-1);
        assert b / x - (-1) == b / x + 1;
        assert b / x - (-1) / x == b / x + 1;
    }
}

lemma DivModProperties(a: int, x: int)
    requires x > 0
    ensures a % x >= 0 && a % x < x
    ensures a == x * (a / x) + (a % x)
{
    // Fundamental properties of division and modulus
}

lemma MultipleCountLemma(current: int, end: int, x: int)
    requires x > 0 && current <= end && current % x == 0 && end % x == 0
    ensures (end - current) / x + 1 == (end / x) - (current / x) + 1
{
    assert current == x * (current / x);
    assert end == x * (end / x);
    calc {
        (end - current) / x + 1;
        == (x * (end / x) - x * (current / x)) / x + 1;
        == x * ((end / x) - (current / x)) / x + 1;
        == (end / x) - (current / x) + 1;
    }
}

lemma RangeAdjustmentLemma(a: int, x: int)
    requires x > 0
    ensures (a + (x - a % x)) % x == 0
{
    DivModProperties(a, x);
    var r := a % x;
    assert a == x * (a / x) + r;
    calc {
        (a + (x - r)) % x;
        == (x * (a / x) + r + (x - r)) % x;
        == (x * (a / x) + x) % x;
        == 0;
    }
}

lemma CountDivisibleInRangeZeroCase(a: int, b: int, x: int)
    requires ValidInput(a, b, x)
    ensures CountDivisibleInRange(a, b, x) >= 0
{
    // The function definition already ensures non-negativity
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
    var current := a;
    if current % x != 0 {
        current := current + (x - current % x);
        RangeAdjustmentLemma(a, x);
    }
    
    var end := b;
    if end % x != 0 {
        end := end - end % x;
    }
    
    if current > end {
        count := 0;
    } else {
        assert current % x == 0 && end % x == 0;
        MultipleCountLemma(current, end, x);
        count := (end - current) / x + 1;
        assert count == (end / x) - (current / x) + 1;
    }
    
    CountDivisibleInRangeLemma(a, b, x);
    CountDivisibleInRangeZeroCase(a, b, x);
    assert count == CountDivisibleInRange(a, b, x);
    assert count >= 0;
}
// </vc-code>

