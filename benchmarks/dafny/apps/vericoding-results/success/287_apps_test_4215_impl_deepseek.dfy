predicate ValidInput(a: int, b: int)
{
    1 <= a <= 100 && 1 <= b <= 100
}

function UncoveredLength(a: int, b: int): int
{
    max(0, a - 2 * b)
}

// <vc-helpers>
function max(a: int, b: int): int
{
    if a > b then a else b
}

lemma MaxLemma(a: int, b: int)
    requires 1 <= a <= 100 && 1 <= b <= 100
    ensures max(0, a - 2 * b) == (if a > 2 * b then a - 2 * b else 0)
{
}

lemma UncoveredLengthLemma(a: int, b: int)
    requires 1 <= a <= 100 && 1 <= b <= 100
    ensures UncoveredLength(a, b) == (if a > 2 * b then a - 2 * b else 0)
{
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
    MaxLemma(a, b);
    UncoveredLengthLemma(a, b);
    
    if a > 2 * b {
        result := a - 2 * b;
    } else {
        result := 0;
    }
}
// </vc-code>

