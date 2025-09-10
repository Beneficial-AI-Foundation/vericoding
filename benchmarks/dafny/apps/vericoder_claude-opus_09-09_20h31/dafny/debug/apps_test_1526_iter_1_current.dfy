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
lemma SortDescendingCorrect(A: int, B: int, C: int)
    ensures var (a0, a1, a2) := SortDescending(A, B, C);
            a0 >= a1 >= a2 && multiset{a0, a1, a2} == multiset{A, B, C}
{
    var (a0, a1, a2) := SortDescending(A, B, C);
    if A >= B && A >= C {
        if B >= C {
            assert (a0, a1, a2) == (A, B, C);
        } else {
            assert (a0, a1, a2) == (A, C, B);
        }
    } else if B >= A && B >= C {
        if A >= C {
            assert (a0, a1, a2) == (B, A, C);
        } else {
            assert (a0, a1, a2) == (B, C, A);
        }
    } else {
        if A >= B {
            assert (a0, a1, a2) == (C, A, B);
        } else {
            assert (a0, a1, a2) == (C, B, A);
        }
    }
}

lemma AllEqualImpliesZeroOps(A: int, B: int, C: int)
    requires ValidInput(A, B, C)
    requires AllEqual(A, B, C)
    ensures MinOperations(A, B, C) == 0
{
    assert A == B == C;
    var (a0, a1, a2) := SortDescending(A, B, C);
    SortDescendingCorrect(A, B, C);
    assert a0 == a1 == a2;
    assert a0 - a1 == 0;
    assert a0 - (a2 + 0) == 0;
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
    var (a0, a1, a2) := SortDescending(A, B, C);
    var gap1 := a0 - a1;
    var updated_smallest := a2 + gap1;
    var remaining_gap := a0 - updated_smallest;
    result := gap1 + remaining_gap / 2 + (remaining_gap % 2) * 2;
    
    // Verify the result matches the function
    assert result == MinOperations(A, B, C);
    
    // Verify AllEqual case
    if AllEqual(A, B, C) {
        AllEqualImpliesZeroOps(A, B, C);
    }
}
// </vc-code>

