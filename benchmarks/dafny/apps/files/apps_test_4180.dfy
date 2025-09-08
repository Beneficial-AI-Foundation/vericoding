Given a cost N yen, calculate the change received when paying with the minimum number of 1000-yen bills.

predicate ValidInput(n: int)
{
    1 <= n <= 10000
}

predicate ValidChange(change: int)
{
    0 <= change <= 999
}

function CorrectChange(n: int): int
    requires ValidInput(n)
{
    (1000 - n % 1000) % 1000
}

method solve(n: int) returns (change: int)
    requires ValidInput(n)
    ensures ValidChange(change)
    ensures change == CorrectChange(n)
{
    change := (1000 - n % 1000) % 1000;
}
