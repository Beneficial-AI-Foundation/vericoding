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
lemma MaxGeMin(A1: int, A2: int, A3: int)
    ensures MaxOfThree(A1, A2, A3) >= MinOfThree(A1, A2, A3)
{
    var m := MinOfThree(A1, A2, A3);
    if m == A1 {
        assert MaxOfThree(A1, A2, A3) >= A1;
    } else if m == A2 {
        assert MaxOfThree(A1, A2, A3) >= A2;
    } else {
        assert m == A3;
        assert MaxOfThree(A1, A2, A3) >= A3;
    }
}

lemma MinCostNonNegative(A1: int, A2: int, A3: int)
    requires ValidInput(A1, A2, A3)
    ensures MinimumCost(A1, A2, A3) >= 0
{
    MaxGeMin(A1, A2, A3);
    calc {
        MinimumCost(A1, A2, A3);
        == MaxOfThree(A1, A2, A3) - MinOfThree(A1, A2, A3);
        >= 0;
    }
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
    MinCostNonNegative(A1, A2, A3);
    return MaxOfThree(A1, A2, A3) - MinOfThree(A1, A2, A3);
}
// </vc-code>

