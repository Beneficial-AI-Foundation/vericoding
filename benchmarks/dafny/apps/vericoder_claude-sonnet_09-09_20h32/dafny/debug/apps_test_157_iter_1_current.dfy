predicate ValidInput(a: int, b: int, c: int)
{
    1 <= a <= 1000 && 1 <= b <= 1000 && 1 <= c <= 1000
}

function MaxRecipeUnits(a: int, b: int, c: int): int
{
    min(a, min(b / 2, c / 4))
}

function TotalFruitsUsed(units: int): int
{
    units * 7
}

// <vc-helpers>
lemma MinProperties(x: int, y: int)
    ensures min(x, y) <= x
    ensures min(x, y) <= y
    ensures min(x, y) == x || min(x, y) == y
{
}

lemma MaxRecipeUnitsNonNegative(a: int, b: int, c: int)
    requires ValidInput(a, b, c)
    ensures MaxRecipeUnits(a, b, c) >= 0
{
    MinProperties(a, min(b / 2, c / 4));
    MinProperties(b / 2, c / 4);
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, c: int) returns (result: int)
    requires ValidInput(a, b, c)
    ensures result == TotalFruitsUsed(MaxRecipeUnits(a, b, c))
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    var maxUnits := MaxRecipeUnits(a, b, c);
    MaxRecipeUnitsNonNegative(a, b, c);
    result := TotalFruitsUsed(maxUnits);
}
// </vc-code>

