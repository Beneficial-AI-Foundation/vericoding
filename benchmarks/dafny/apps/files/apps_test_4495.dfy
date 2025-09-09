Given nonnegative integers a and b (where a ≤ b) and a positive integer x,
count how many integers in the range [a, b] inclusive are divisible by x.

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

method CountDivisible(a: int, b: int, x: int) returns (count: int)
    requires ValidInput(a, b, x)
    ensures count == CountDivisibleInRange(a, b, x)
    ensures count >= 0
{
    if a == 0 {
        count := b / x + 1;
    } else {
        count := b / x - (a - 1) / x;
    }
}
