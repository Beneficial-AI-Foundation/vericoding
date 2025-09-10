predicate ValidInput(N: int, D: int)
{
  N >= 1 && N <= 20 && D >= 1 && D <= 20
}

function CoverageRange(position: int, D: int): (int, int)
{
  (position - D, position + D)
}

predicate TreesCovered(N: int, D: int, inspectors: int)
{
  inspectors >= 1 && inspectors <= N && inspectors == ((N - 1) / (2 * D + 1)) + 1
}

// <vc-helpers>
function MinInspectors(N: int, D: int): int
  requires ValidInput(N, D)
{
  ((N - 1) / (2 * D + 1)) + 1
}

ghost method LemMinInspectorsEqTreesCovered(N: int, D: int)
  requires ValidInput(N, D)
  ensures TreesCovered(N, D, MinInspectors(N, D))
{
  assert 2 * D + 1 >= 1;
  var denom := 2 * D + 1;
  calc {
    MinInspectors(N, D);
    == ((N - 1) / denom) + 1;
    == { assert forall x: int, y: int :: y > 0 ==> (x / y) + 1 == ((x + y - 1) / y); } (((N - 1) + denom - 1) / denom);
    == (N + denom - 2) / denom;
  }
  assert forall x: int :: 0 <= x < denom ==> (x / denom) == 0;
  // Standard ceiling properties
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
method InspectorsRequired(N: int, D: int) returns (k: int)
  requires ValidInput(N, D)
  ensures TreesCovered(N, D, k)
{
  k := ((N - 1) / (2 * D + 1)) + 1;
}

// Method body for suggestion, but adjusted signature based on helpers. Actual method implemented as above.
} ```
// </vc-code>

