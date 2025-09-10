predicate ValidInput(a: int, b: int)
{
    1 <= a <= 100 && 1 <= b <= 100
}

function UncoveredLength(a: int, b: int): int
{
    max(0, a - 2 * b)
}

// <vc-helpers>
function max(x: int, y: int): int
{
    if x >= y then x else y
}

lemma MaxProperties(x: int, y: int)
    ensures max(x, y) == x || max(x, y) == y
    ensures max(x, y) >= x && max(x, y) >= y
    ensures max(x, y) == x <==> x >= y
    ensures max(x, y) == y <==> y >= x
{
}

lemma UncoveredLengthEquivalence(a: int, b: int)
    ensures UncoveredLength(a, b) == (if a > 2 * b then a - 2 * b else 0)
{
    MaxProperties(0, a - 2 * b);
    if a > 2 * b {
        assert a - 2 * b > 0;
        assert max(0, a - 2 * b) == a - 2 * b;
    } else {
        assert a - 2 * b <= 0;
        assert max(0, a - 2 * b) == 0;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: int)
    requires ValidInput(a, b)
    ensures result >= 0
    ensures result == UncoveredLength(a, b)
    ensures result == if a > 2 * b then a - 2 * b else 0
// </vc-spec>
// <vc-code>
{
    UncoveredLengthEquivalence(a, b);
    if a > 2 * b {
        result := a - 2 * b;
    } else {
        result := 0;
    }
}
// </vc-code>

