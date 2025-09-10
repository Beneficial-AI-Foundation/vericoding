/*
Given N students, divide them into groups such that the number of groups 
containing 3 or more students is maximized. Groups with 2 or fewer students 
are not counted toward the result.
*/

predicate ValidInput(n: int) {
    1 <= n <= 1000
}

function MaxGroupsWithAtLeastThree(n: int): int
    requires ValidInput(n)
{
    n / 3
}

predicate ValidSolution(n: int, result: int) 
    requires ValidInput(n)
{
    result == MaxGroupsWithAtLeastThree(n) &&
    result >= 0 &&
    result <= n
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
