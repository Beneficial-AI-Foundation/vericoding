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
        assert b / x + 1 == b / x - (-1) / x;
        assert (-1) / x == -1;  // Since x > 0, -1/x = -1
        assert b / x - (-1) == b / x + 1;
    }
}

lemma DivModProperties(a: int, x: int)
    requires x > 0
    ensures a % x >= 0 && a % x < x
    ensures a == x * (a / x) + (a % x)
{
    // Fundamental properties of division and modulus
}

lemma MultipleCountLemma(first: int, last: int, x: int)
    requires x > 0 && first <= last && first % x == 0 && last % x == 0
    ensures (last - first) / x + 1 == (last / x) - (first / x) + 1
{
}

lemma RangeAdjustmentLemma(a: int, x: int)
    requires x > 0
    ensures (a + (x - a % x)) % x == 0
{
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
    count := CountDivisibleInRange(a, b, x);
}
// </vc-code>

