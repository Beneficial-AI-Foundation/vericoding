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
    if A1 >= A2 && A1 >= A3 {
        assert MaxOfThree(A1, A2, A3) == A1;
        if A1 <= A2 && A1 <= A3 {
            assert MinOfThree(A1, A2, A3) == A1;
            assert MaxOfThree(A1, A2, A3) >= MinOfThree(A1, A2, A3);
        } else if A2 <= A3 {
            assert MinOfThree(A1, A2, A3) == A2;
            assert A1 >= A2;
            assert MaxOfThree(A1, A2, A3) >= MinOfThree(A1, A2, A3);
        } else {
            assert MinOfThree(A1, A2, A3) == A3;
            assert A1 >= A3;
            assert MaxOfThree(A1, A2, A3) >= MinOfThree(A1, A2, A3);
        }
    } else if A2 >= A3 {
        assert MaxOfThree(A1, A2, A3) == A2;
        if A1 <= A2 && A1 <= A3 {
            assert MinOfThree(A1, A2, A3) == A1;
            assert A2 >= A1;
            assert MaxOfThree(A1, A2, A3) >= MinOfThree(A1, A2, A3);
        } else if A2 <= A3 {
            assert MinOfThree(A1, A2, A3) == A2;
            assert MaxOfThree(A1, A2, A3) >= MinOfThree(A1, A2, A3);
        } else {
            assert MinOfThree(A1, A2, A3) == A3;
            assert A2 >= A3;
            assert MaxOfThree(A1, A2, A3) >= MinOfThree(A1, A2, A3);
        }
    } else {
        assert MaxOfThree(A1, A2, A3) == A3;
        if A1 <= A2 && A1 <= A3 {
            assert MinOfThree(A1, A2, A3) == A1;
            assert A3 >= A1;
            assert MaxOfThree(A1, A2, A3) >= MinOfThree(A1, A2, A3);
        } else if A2 <= A3 {
            assert MinOfThree(A1, A2, A3) == A2;
            assert A3 >= A2;
            assert MaxOfThree(A1, A2, A3) >= MinOfThree(A1, A2, A3);
        } else {
            assert MinOfThree(A1, A2, A3) == A3;
            assert MaxOfThree(A1, A2, A3) >= MinOfThree(A1, A2, A3);
        }
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
  MaxGeMin(A1, A2, A3);
  result := MinimumCost(A1, A2, A3);
  assert result >= 0;
}
// </vc-code>

