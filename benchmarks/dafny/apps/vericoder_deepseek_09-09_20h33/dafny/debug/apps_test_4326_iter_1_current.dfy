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
lemma MaxGroupsLemma(n: int)
    requires ValidInput(n)
    ensures n / 3 >= 0 && n / 3 <= n
{
}

lemma DivisionProperties(n: int)
    requires ValidInput(n)
    ensures n / 3 <= n
{
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
    var result := n / 3;
    assert result >= 0 by {
        MaxGroupsLemma(n);
    }
    assert result <= n by {
        DivisionProperties(n);
    }
    return result;
}
// </vc-code>

