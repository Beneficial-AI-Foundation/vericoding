Given a positive integer N, find the smallest positive integer that is divisible by both 2 and N.
This is equivalent to finding the least common multiple of 2 and N.

predicate ValidInput(n: int)
{
    n >= 1
}

predicate DivisibleByBoth(result: int, n: int)
    requires n >= 1
{
    result % 2 == 0 && result % n == 0
}

predicate IsSmallest(result: int, n: int)
    requires n >= 1
{
    forall k: int :: 1 <= k < result ==> !(k % 2 == 0 && k % n == 0)
}

function LCM(a: int, b: int): int
    requires a >= 1 && b >= 1
{
    if a % b == 0 then a
    else if b % a == 0 then b
    else a * b
}

method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result >= 1
    ensures DivisibleByBoth(result, n)
    ensures IsSmallest(result, n)
    ensures (n % 2 == 0 ==> result == n) && (n % 2 != 0 ==> result == n * 2)
{
    if n % 2 == 0 {
        result := n;
        assert forall k: int :: 1 <= k < n ==> k % n != 0;
    } else {
        result := n * 2;
        assert forall k: int :: 1 <= k < n * 2 ==> (k % n == 0 ==> k == n);
        assert n % 2 != 0;
        assert forall k: int :: 1 <= k < n * 2 ==> !(k % 2 == 0 && k % n == 0);
    }
}
