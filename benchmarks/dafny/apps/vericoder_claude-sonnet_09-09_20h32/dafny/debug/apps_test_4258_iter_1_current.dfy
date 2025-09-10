predicate ValidInput(A: int, B: int, T: int)
{
    1 <= A <= 20 && 1 <= B <= 20 && 1 <= T <= 20
}

function ProductionCount(A: int, T: int): int
    requires A > 0
{
    T / A
}

function TotalBiscuits(A: int, B: int, T: int): int
    requires A > 0
{
    B * ProductionCount(A, T)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, T: int) returns (result: int)
    requires ValidInput(A, B, T)
    ensures result == TotalBiscuits(A, B, T)
// </vc-spec>
// <vc-code>
{
    result := B * (T / A);
}
// </vc-code>

