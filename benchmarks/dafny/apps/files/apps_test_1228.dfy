Given a current HP value, determine how much to increase it (by 0, 1, or 2) to achieve the highest possible category.
HP categories are defined by remainder when divided by 4:
Category A: remainder 1 (highest priority), Category B: remainder 3, Category C: remainder 2, Category D: remainder 0 (lowest priority)
Priority order: A > B > C > D

function GetCategory(hp: int): char
{
    var remainder := hp % 4;
    if remainder == 1 then 'A'
    else if remainder == 3 then 'B'
    else if remainder == 2 then 'C'
    else 'D'
}

predicate ValidInput(n: int)
{
    30 <= n <= 100
}

predicate ValidOutput(a: int, b: char)
{
    0 <= a <= 2 && (b == 'A' || b == 'B' || b == 'C' || b == 'D')
}

predicate OptimalChoice(n: int, a: int, b: char)
{
    b == GetCategory(n + a) &&
    ((n % 4 == 1) ==> (a == 0 && b == 'A')) &&
    ((n % 4 == 2) ==> (a == 1 && b == 'B')) &&
    ((n % 4 == 3) ==> (a == 2 && b == 'A')) &&
    ((n % 4 == 0) ==> (a == 1 && b == 'A'))
}

method solve(n: int) returns (a: int, b: char)
    requires ValidInput(n)
    ensures ValidOutput(a, b)
    ensures OptimalChoice(n, a, b)
    ensures b == 'A' || b == 'B'
{
    var remainder := n % 4;
    if remainder == 1 {
        a := 0;
        b := 'A';
    } else if remainder == 2 {
        a := 1;
        b := 'B';
    } else if remainder == 3 {
        a := 2;
        b := 'A';
    } else { // remainder == 0
        a := 1;
        b := 'A';
    }
}
