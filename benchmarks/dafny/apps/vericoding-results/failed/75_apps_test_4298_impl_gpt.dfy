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

// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  var denom := 2 * D + 1;
  inspectors := ((N - 1) / denom) + 1;

  // Prove inspectors >= 1
  assert denom >= 1;
  assert N - 1 >= 0;
  assert ((N - 1) / denom) >= 0;
  assert inspectors >= 1;

  // Prove inspectors <= N
  var q := (N - 1) / denom;
  assert (N - 1) == denom * q + ((N - 1) % denom);
  assert ((N - 1) % denom) >= 0;
  assert denom * q <= N - 1;

  assert denom - 1 >= 0;
  assert (denom - 1) * q >= 0;
  assert q <= q + (denom - 1) * q;
  assert q + (denom - 1) * q == denom * q;
  assert q <= N - 1;

  assert inspectors <= N;
}
// </vc-code>

