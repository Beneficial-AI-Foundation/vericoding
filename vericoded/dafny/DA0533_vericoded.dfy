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

// </vc-helpers>

// <vc-spec>
method solve(A1: int, A2: int, A3: int) returns (result: int)
    requires ValidInput(A1, A2, A3)
    ensures result >= 0
    ensures result == MinimumCost(A1, A2, A3)
// </vc-spec>
// <vc-code>
{
    var max := A1;
    var min := A1;
    
    if A2 > max {
        max := A2;
    }
    if A3 > max {
        max := A3;
    }
    
    if A2 < min {
        min := A2;
    }
    if A3 < min {
        min := A3;
    }
    
    result := max - min;
}
// </vc-code>

