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
lemma MaxGroupsProperties(n: int)
    requires ValidInput(n)
    ensures MaxGroupsWithAtLeastThree(n) >= 0
    ensures MaxGroupsWithAtLeastThree(n) <= n
{
    assert n >= 1;
    assert n / 3 >= 0;
    assert n / 3 <= n;
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
    MaxGroupsProperties(n);
    return n / 3;
}
// </vc-code>

