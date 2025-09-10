predicate ValidInput(A: int, B: int, C: int, D: int)
{
    1 <= A <= 10000 && 1 <= B <= 10000 && 1 <= C <= 10000 && 1 <= D <= 10000
}

function MaxArea(A: int, B: int, C: int, D: int): int
{
    if A * B >= C * D then A * B else C * D
}

// <vc-helpers>
lemma MaxAreaLemma(A: int, B: int, C: int, D: int)
  requires ValidInput(A, B, C, D)
  ensures MaxArea(A, B, C, D) >= A * B
  ensures MaxArea(A, B, C, D) >= C * D
  ensures MaxArea(A, B, C, D) == A * B || MaxArea(A, B, C, D) == C * D
{}
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
  if A * B >= C * D {
    result := A * B;
  } else {
    result := C * D;
  }
}
// </vc-code>

