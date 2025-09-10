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
lemma SortDescendingSorted(A: int, B: int, C: int)
  ensures SortDescending(A, B, C).0 >= SortDescending(A, B, C).1
  ensures SortDescending(A, B, C).1 >= SortDescending(A, B, C).2
{
  if A >= B && A >= C {
    if B >= C {
      assert SortDescending(A, B, C) == (A, B, C);
      assert SortDescending(A, B, C).0 >= SortDescending(A, B, C).1; // A >= B
      assert SortDescending(A, B, C).1 >= SortDescending(A, B, C).2; // B >= C
    } else {
      assert SortDescending(A, B, C) == (A, C, B);
      assert SortDescending(A, B, C).0 >= SortDescending(A, B, C).1; // A >= C
      assert SortDescending(A, B, C).1 >= SortDescending(A, B, C).2; // C >= B
    }
  } else if B >= A && B >= C {
    if A >= C {
      assert SortDescending(A, B, C) == (B, A, C);
      assert SortDescending(A, B, C).0 >= SortDescending(A, B, C).1; // B >= A
      assert SortDescending(A, B, C).1 >= SortDescending(A, B, C).2; // A >= C
    } else {
      assert SortDescending(A, B, C) == (B, C, A);
      assert SortDescending(A, B, C).0 >= SortDescending(A, B, C).1; // B >= C
      assert SortDescending(A, B, C).1 >= SortDescending(A, B, C).2; // C >= A
    }
  } else {
    if A >= B {
      assert SortDescending(A, B, C) == (C, A, B);
      assert SortDescending(A, B, C).0 >= SortDescending(A, B, C).1; // C >= A
      assert SortDescending(A, B, C).1 >= SortDescending(A, B, C).2; // A >= B
    } else {
      assert SortDescending(A, B, C) == (C, B, A);
      assert SortDescending(A, B, C).0 >= SortDescending(A, B, C).1; // C >= B
      assert SortDescending(A, B, C).1 >= SortDescending(A, B, C).2; // B >= A
    }
  }
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
  SortDescendingSorted(A, B, C);
  var a0 := SortDescending(A, B, C).0;
  var a1 := SortDescending(A, B, C).1;
  var a2 := SortDescending(A, B, C).2;

  assert a0 >= a1 && a1 >= a2;

  var gap1 := a0 - a1;
  assert gap1 >= 0;

  var updated_smallest := a2 + gap1;
  var remaining_gap := a0 - updated_smallest;
  assert remaining_gap == a1 - a2;
  assert remaining_gap >= 0;

  result := gap1 + remaining_gap / 2 + (remaining_gap % 2) * 2;

  assert result == MinOperations(A, B, C);

  assert result >= 0;

  if AllEqual(A, B, C) {
    assert result == 0;
  }
}
// </vc-code>

