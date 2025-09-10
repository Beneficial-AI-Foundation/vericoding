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
method MaxGroups(n: int) returns (r: int)
    requires ValidInput(n)
    ensures ValidSolution(n, r)
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
    r := n / 3;
}
// </vc-code>

