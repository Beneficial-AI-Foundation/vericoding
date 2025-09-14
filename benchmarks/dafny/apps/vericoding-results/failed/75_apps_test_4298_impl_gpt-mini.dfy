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
lemma InspectorsBound(N: int, D: int)
  requires ValidInput(N, D)
  ensures ((N - 1) / (2 * D + 1)) + 1 >= 1 && ((N - 1) / (2 * D + 1)) + 1 <= N
{
  var q := (N - 1) / (2 * D + 1);
  var r := (N - 1) % (2 * D + 1);
  assert N - 1 == q * (2 * D + 1) + r;
  assert 0 <= r;
  assert q >= 0;
  assert 2 * D + 1 >= 1;
  // From decomposition and r >= 0, q * (2*D+1) <= N-1
  assert q * (2 * D + 1) <= N - 1;
  // Since q >= 0 and (2*D+1) >= 1, q <= q*(2*D+1)
  assert q <= q * (2 * D + 1);
  // Hence q <= N-1, so q+1 <= N
  assert q <= N - 1;
  assert q + 1 <= N;
  // And q >= 0 implies q+1 >= 1
  assert q + 1 >= 1;
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  var inspectors := ((N - 1) / (2 * D + 1)) + 1;
  InspectorsBound(N, D);
  return inspectors;
}
// </vc-code>

