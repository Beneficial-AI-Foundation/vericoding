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
lemma SortDescendingIsDescending(A: int, B: int, C: int)
    requires ValidInput(A, B, C)
    ensures SortDescending(A, B, C).0 >= SortDescending(A, B, C).1 &&
            SortDescending(A, B, C).1 >= SortDescending(A, B, C).2
{
    var (a0, a1, a2) := SortDescending(A, B, C);
    if A >= B && A >= C {
        if B >= C {
            assert a0 == A && a1 == B && a2 == C;
            assert a0 >= a1;
            assert a1 >= a2;
        } else {
            // B < C
            assert a0 == A && a1 == C && a2 == B;
            assert a0 >= a1;
            assert a1 >= a2;
        }
    } else if B >= A && B >= C {
        if A >= C {
            assert a0 == B && a1 == A && a2 == C;
            assert a0 >= a1;
            assert a1 >= a2;
        } else {
            // A < C
            assert a0 == B && a1 == C && a2 == A;
            assert a0 >= a1;
            assert a1 >= a2;
        }
    } else {
        // C is largest
        if A >= B {
            assert a0 == C && a1 == A && a2 == B;
            assert a0 >= a1;
            assert a1 >= a2;
        } else {
            assert a0 == C && a1 == B && a2 == A;
            assert a0 >= a1;
            assert a1 >= a2;
        }
    }
}

lemma MinOperationsNonNegative(A: int, B: int, C: int)
    requires ValidInput(A, B, C)
    ensures MinOperations(A, B, C) >= 0
{
    var (a0, a1, a2) := SortDescending(A, B, C);
    SortDescendingIsDescending(A, B, C);
    var gap1 := a0 - a1;
    var updated_smallest := a2 + gap1;
    var remaining_gap := a0 - updated_smallest;
    // From ordering a0 >= a1 >= a2 we get gap1 >= 0 and remaining_gap = a1 - a2 >= 0
    assert gap1 >= 0;
    assert remaining_gap == a1 - a2;
    assert remaining_gap >= 0;
    // Unfold MinOperations and conclude non-negativity
    assert MinOperations(A, B, C) == gap1 + remaining_gap / 2 + (remaining_gap % 2) * 2;
    assert gap1 + remaining_gap / 2 + (remaining_gap % 2) * 2 >= 0;
}

lemma MinOperationsZeroIfAllEqual(A: int, B: int, C: int)
    requires ValidInput(A, B, C) && AllEqual(A, B, C)
    ensures MinOperations(A, B, C) == 0
{
    // When all equal, SortDescending returns (A, A, A)
    var (a0, a1, a2) := SortDescending(A, B, C);
    // Because A == B == C, the first branch of SortDescending is taken and inner branch too,
    // yielding (A, B, C) == (A, A, A).
    assert A == B && B == C;
    assert a0 == A && a1 == B && a2 == C;
    var gap1 := a0 - a1;
    var updated_smallest := a2 + gap1;
    var remaining_gap := a0 - updated_smallest;
    assert gap1 == 0;
    assert remaining_gap == 0;
    assert MinOperations(A, B, C) == 0;
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
  result := MinOperations(A, B, C);
  MinOperationsNonNegative(A, B, C);
  assert result >= 0;
  if AllEqual(A, B, C) {
    MinOperationsZeroIfAllEqual(A, B, C);
    assert result == 0;
  }
}
// </vc-code>

