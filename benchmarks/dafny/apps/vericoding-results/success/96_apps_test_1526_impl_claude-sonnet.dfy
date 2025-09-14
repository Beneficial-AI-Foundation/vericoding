predicate ValidInput(A: int, B: int, C: int) {
    0 <= A <= 50 && 0 <= B <= 50 && 0 <= C <= 50
}

function MaxOf3(A: int, B: int, C: int): int {
    if A >= B && A >= C then A
    else if B >= C then B
    else C
}

function SortDescending(A: int, B: int, C: int): (int, int, int) {
    if A >= B && A >= C then
        if B >= C then (A, B, C) else (A, C, B)
    else if B >= A && B >= C then
        if A >= C then (B, A, C) else (B, C, A)
    else
        if A >= B then (C, A, B) else (C, B, A)
}

function MinOperations(A: int, B: int, C: int): int
    requires ValidInput(A, B, C)
{
    var (a0, a1, a2) := SortDescending(A, B, C);
    var gap1 := a0 - a1;
    var updated_smallest := a2 + gap1;
    var remaining_gap := a0 - updated_smallest;
    gap1 + remaining_gap / 2 + (remaining_gap % 2) * 2
}

predicate AllEqual(A: int, B: int, C: int) {
    A == B && B == C
}

// <vc-helpers>
lemma SortDescendingProperties(A: int, B: int, C: int)
    ensures var (a0, a1, a2) := SortDescending(A, B, C); a0 >= a1 >= a2
    ensures var (a0, a1, a2) := SortDescending(A, B, C); a0 == MaxOf3(A, B, C)
    ensures var (a0, a1, a2) := SortDescending(A, B, C); multiset{a0, a1, a2} == multiset{A, B, C}
{
}

lemma MinOperationsNonNegative(A: int, B: int, C: int)
    requires ValidInput(A, B, C)
    ensures MinOperations(A, B, C) >= 0
{
    var (a0, a1, a2) := SortDescending(A, B, C);
    SortDescendingProperties(A, B, C);
    assert a0 >= a1 >= a2;
    var gap1 := a0 - a1;
    assert gap1 >= 0;
    var updated_smallest := a2 + gap1;
    var remaining_gap := a0 - updated_smallest;
    assert remaining_gap >= 0;
}

lemma AllEqualImpliesZeroOperations(A: int, B: int, C: int)
    requires ValidInput(A, B, C)
    requires AllEqual(A, B, C)
    ensures MinOperations(A, B, C) == 0
{
    assert A == B && B == C;
    var (a0, a1, a2) := SortDescending(A, B, C);
    assert a0 == a1 && a1 == a2;
    var gap1 := a0 - a1;
    assert gap1 == 0;
    var updated_smallest := a2 + gap1;
    assert updated_smallest == a2;
    var remaining_gap := a0 - updated_smallest;
    assert remaining_gap == 0;
}
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, C: int) returns (result: int)
    requires ValidInput(A, B, C)
    ensures result >= 0
    ensures AllEqual(A, B, C) ==> result == 0
    ensures result == MinOperations(A, B, C)
// </vc-spec>
// <vc-code>
{
    MinOperationsNonNegative(A, B, C);
    if AllEqual(A, B, C) {
        AllEqualImpliesZeroOperations(A, B, C);
    }
    result := MinOperations(A, B, C);
}
// </vc-code>

