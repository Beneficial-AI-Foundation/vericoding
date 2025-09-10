predicate ValidInput(A: int, B: int, C: int, D: int)
{
    1 <= A <= 10000 && 1 <= B <= 10000 && 1 <= C <= 10000 && 1 <= D <= 10000
}

function MaxArea(A: int, B: int, C: int, D: int): int
{
    if A * B >= C * D then A * B else C * D
}

// <vc-helpers>
function Max(a: int, b: int): int
  ensures Max(a, b) == a || Max(a, b) == b
  ensures Max(a, b) >= a && Max(a, b) >= b
{
  if a >= b then a else b
}
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
  var area1 := A * B;
  var area2 := C * D;
  result := Max(area1, area2);
  assert result == MaxArea(A, B, C, D);
}
// </vc-code>

