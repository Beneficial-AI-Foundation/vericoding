Given two time intervals [A, B) and [C, D), find the length of their intersection.
Alice holds a button from time A to time B (exclusive).
Bob holds a button from time C to time D (exclusive).
Calculate how many seconds both are holding their buttons simultaneously.

predicate ValidInput(a: int, b: int, c: int, d: int)
{
    0 <= a < b <= 100 && 0 <= c < d <= 100
}

function min(x: int, y: int): int
{
    if x < y then x else y
}

function max(x: int, y: int): int
{
    if x > y then x else y
}

function IntervalOverlapLength(a: int, b: int, c: int, d: int): int
{
    if min(b, d) - max(a, c) > 0 then min(b, d) - max(a, c) else 0
}

method solve(a: int, b: int, c: int, d: int) returns (result: int)
    requires ValidInput(a, b, c, d)
    ensures result >= 0
    ensures result == IntervalOverlapLength(a, b, c, d)
    ensures result <= 100
{
    var s := if a > c then a else c;
    var e := if b < d then b else d;
    result := if e - s > 0 then e - s else 0;
}
