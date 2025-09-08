Given the number of lemons (a), apples (b), and pears (c), find the maximum total number of fruits
that can be used to make a compote following the recipe ratio of 1:2:4 (lemons:apples:pears).
Fruits must be used whole and cannot be cut or broken. If no complete recipe units can be made, output 0.

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

function min(x: int, y: int): int
{
    if x <= y then x else y
}

method solve(a: int, b: int, c: int) returns (result: int)
    requires ValidInput(a, b, c)
    ensures result == TotalFruitsUsed(MaxRecipeUnits(a, b, c))
    ensures result >= 0
{
    var units := MaxRecipeUnits(a, b, c);
    result := TotalFruitsUsed(units);
}
