predicate ValidInput(A1: int, A2: int, A3: int)
{
    1 <= A1 <= 100 && 1 <= A2 <= 100 && 1 <= A3 <= 100
}

function MaxOfThree(A1: int, A2: int, A3: int): int
{
    if A1 >= A2 && A1 >= A3 then A1 else if A2 >= A3 then A2 else A3
}

function MinOfThree(A1: int, A2: int, A3: int): int
{
    if A1 <= A2 && A1 <= A3 then A1 else if A2 <= A3 then A2 else A3
}

function MinimumCost(A1: int, A2: int, A3: int): int
{
    MaxOfThree(A1, A2, A3) - MinOfThree(A1, A2, A3)
}

// <vc-helpers>
lemma MaxOfThreeProperties(A1: int, A2: int, A3: int)
    ensures MaxOfThree(A1, A2, A3) >= A1
    ensures MaxOfThree(A1, A2, A3) >= A2
    ensures MaxOfThree(A1, A2, A3) >= A3
    ensures MaxOfThree(A1, A2, A3) == A1 || MaxOfThree(A1, A2, A3) == A2 || MaxOfThree(A1, A2, A3) == A3
{
}

lemma MinOfThreeProperties(A1: int, A2: int, A3: int)
    ensures MinOfThree(A1, A2, A3) <= A1
    ensures MinOfThree(A1, A2, A3) <= A2
    ensures MinOfThree(A1, A2, A3) <= A3
    ensures MinOfThree(A1, A2, A3) == A1 || MinOfThree(A1, A2, A3) == A2 || MinOfThree(A1, A2, A3) == A3
{
}

lemma MinimumCostNonNegative(A1: int, A2: int, A3: int)
    ensures MinimumCost(A1, A2, A3) >= 0
{
    MaxOfThreeProperties(A1, A2, A3);
    MinOfThreeProperties(A1, A2, A3);
}
// </vc-helpers>

// <vc-spec>
method solve(A1: int, A2: int, A3: int) returns (result: int)
    requires ValidInput(A1, A2, A3)
    ensures result >= 0
    ensures result == MinimumCost(A1, A2, A3)
// </vc-spec>
// <vc-code>
{
    MinimumCostNonNegative(A1, A2, A3);
    result := MaxOfThree(A1, A2, A3) - MinOfThree(A1, A2, A3);
}
// </vc-code>

