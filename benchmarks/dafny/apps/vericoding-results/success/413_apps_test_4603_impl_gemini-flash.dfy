// <vc-preamble>
predicate ValidInput(A: int, B: int, C: int, D: int)
{
    1 <= A <= 1000 && 1 <= B <= 1000 && 1 <= C <= 1000 && 1 <= D <= 1000
}

function MinTotalFare(A: int, B: int, C: int, D: int): int
{
    (if A < B then A else B) + (if C < D then C else D)
}
// </vc-preamble>

// <vc-helpers>
predicate Min(a: int, b: int, result: int) {
    (a < b && result == a) || (b <= a && result == b)
}
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, C: int, D: int) returns (result: int)
    requires ValidInput(A, B, C, D)
    ensures result == MinTotalFare(A, B, C, D)
// </vc-spec>
// <vc-code>
{
  var fareAB: int;
  if A < B {
    fareAB := A;
  } else {
    fareAB := B;
  }

  var fareCD: int;
  if C < D {
    fareCD := C;
  } else {
    fareCD := D;
  }

  result := fareAB + fareCD;
}
// </vc-code>
