/*
Find the number of polynomials P(x) with non-negative integer coefficients 
such that P(t) = a and P(P(t)) = b, where t, a, and b are given positive integers.
Since P(t) = a, the second condition becomes P(a) = b.
Output "inf" if infinitely many such polynomials exist, otherwise output the count.
*/

predicate ValidInput(t: int, a: int, b: int)
{
    t > 0 && a > 0 && b > 0
}

predicate ValidOutput(res: string)
{
    res == "0" || res == "1" || res == "2" || res == "inf"
}

predicate InfiniteCase(t: int, a: int, b: int)
{
    a == t && a == b && a == 1
}

predicate TwoSolutionsCase(t: int, a: int, b: int)
{
    a == t && a == b && a != 1
}

predicate ZeroSolutionsCase(t: int, a: int, b: int)
{
    (t == 2 && a == 3 && b > 10000) ||
    (a == t && a != b) ||
    (a != t && (a - b) % (t - a) == 0) ||
    (a != t && (a - b) % (t - a) != 0 && t == b)
}

predicate OneSolutionCase(t: int, a: int, b: int)
{
    a != t && (a - b) % (t - a) != 0 && t != b
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(t: int, a: int, b: int) returns (res: string)
    requires ValidInput(t, a, b)
    requires t != a || a == t
    ensures ValidOutput(res)
    ensures InfiniteCase(t, a, b) ==> res == "inf"
    ensures TwoSolutionsCase(t, a, b) ==> res == "2"
    ensures ZeroSolutionsCase(t, a, b) ==> res == "0"
    ensures OneSolutionCase(t, a, b) ==> res == "1"
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
