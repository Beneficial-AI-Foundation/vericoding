predicate ValidInput(A: int, B: int, C: int, D: int)
{
    1 <= A <= 1000 && 1 <= B <= 1000 && 1 <= C <= 1000 && 1 <= D <= 1000
}

function MinTotalFare(A: int, B: int, C: int, D: int): int
{
    (if A < B then A else B) + (if C < D then C else D)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, C: int, D: int) returns (result: int)
    requires ValidInput(A, B, C, D)
    ensures result == MinTotalFare(A, B, C, D)
// </vc-spec>
// <vc-code>
{
    var minAB := if A < B then A else B;
    var minCD := if C < D then C else D;
    result := minAB + minCD;
}
// </vc-code>

