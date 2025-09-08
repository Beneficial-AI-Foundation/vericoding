Find the greatest common divisor of all integers in the range [a, b] inclusive,
where 1 ≤ a ≤ b. If a = b, the GCD is a. If a < b, the GCD is 1 since
consecutive integers are coprime.

predicate ValidInput(a: int, b: int)
{
    1 <= a <= b
}

function GcdOfRange(a: int, b: int): int
    requires ValidInput(a, b)
{
    if a == b then a else 1
}

method solve(a: int, b: int) returns (result: int)
    requires ValidInput(a, b)
    ensures result == GcdOfRange(a, b)
    ensures a == b ==> result == a
    ensures a < b ==> result == 1
{
    if a == b {
        result := a;
    } else {
        result := 1;
    }
}
