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
lemma MaxGroupsCorrect(n: int)
    requires ValidInput(n)
    ensures ValidSolution(n, n / 3)
{
    // The solution n/3 is valid by definition of ValidSolution
    // since ValidSolution checks that result == MaxGroupsWithAtLeastThree(n)
    // and MaxGroupsWithAtLeastThree(n) returns n/3
}

method ComputeMaxGroups(n: int) returns (result: int)
    requires ValidInput(n)
    ensures ValidSolution(n, result)
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
    result := n / 3;
    MaxGroupsCorrect(n);
}
// </vc-code>

