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
lemma CountDivisibleNonNegative(a: int, b: int, x: int)
    requires ValidInput(a, b, x)
    ensures if a == 0 then b / x + 1 >= 0 else (if b / x >= (a - 1) / x then b / x - (a - 1) / x >= 0 else 0 >= 0)
{
    // This lemma helps establish that our count is non-negative
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
        var result := b / x - (a - 1) / x;
        if result >= 0 {
            count := result;
        } else {
            count := 0;
        }
    }
}
// </vc-code>

