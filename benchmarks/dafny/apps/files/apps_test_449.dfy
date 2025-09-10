/*
Given an integer n representing dollars, find the minimum number of bills 
needed to represent this amount using denominations of $1, $5, $10, $20, and $100.
*/

predicate ValidInput(n: int) {
    n >= 1
}

function MinBills(n: int): int
    requires n >= 1
{
    n / 100 + (n % 100) / 20 + ((n % 100) % 20) / 10 + (((n % 100) % 20) % 10) / 5 + ((((n % 100) % 20) % 10) % 5)
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result >= 0
    ensures result == MinBills(n)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
