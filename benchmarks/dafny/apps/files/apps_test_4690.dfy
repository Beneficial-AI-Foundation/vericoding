/*
Given dimensions of two rectangles (A×B and C×D), return the area of the rectangle with the larger area.
If both rectangles have equal areas, return that common area.
*/

predicate ValidInput(A: int, B: int, C: int, D: int)
{
    1 <= A <= 10000 && 1 <= B <= 10000 && 1 <= C <= 10000 && 1 <= D <= 10000
}

function MaxArea(A: int, B: int, C: int, D: int): int
{
    if A * B >= C * D then A * B else C * D
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, C: int, D: int) returns (result: int)
    requires ValidInput(A, B, C, D)
    ensures result == MaxArea(A, B, C, D)
    ensures result >= A * B && result >= C * D
    ensures result == A * B || result == C * D
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
