This verification task implements the computation of the sum of all integers from 1 to n inclusive, where n is a positive integer. The expected implementation should use the well-known mathematical formula n*(n+1)/2 for efficiency.

// ======= TASK =======
// Given a positive integer n, compute the sum of all integers from 1 to n inclusive.

// ======= SPEC REQUIREMENTS =======
predicate ValidInput(n: int)
{
    n >= 1
}

function SumFromOneToN(n: int): int
    requires n >= 1
{
    n * (n + 1) / 2
}

// ======= HELPERS =======

method sum_to_n(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == SumFromOneToN(n)
{
    result := n * (n + 1) / 2;
}
