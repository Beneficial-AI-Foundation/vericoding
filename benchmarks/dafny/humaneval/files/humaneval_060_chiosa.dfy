// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
// ======= HELPERS =======
// </vc-helpers>

// <vc-spec>
method sum_to_n(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == SumFromOneToN(n)
// </vc-spec>
// <vc-code>
{
    result := n * (n + 1) / 2;
}
// </vc-code>
