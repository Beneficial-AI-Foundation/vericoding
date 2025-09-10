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
lemma CoverageFormula(N: int, D: int)
  requires ValidInput(N, D)
  ensures ((N - 1) / (2 * D + 1)) + 1 >= 1
  ensures ((N - 1) / (2 * D + 1)) + 1 <= N
{
  // The minimum is 1 (when D is large enough to cover all trees)
  assert ((N - 1) / (2 * D + 1)) >= 0;
  assert ((N - 1) / (2 * D + 1)) + 1 >= 1;
  
  // The maximum is N (when D = 0, but D >= 1 so this is bounded)
  if (2 * D + 1) >= N {
    assert (N - 1) / (2 * D + 1) == 0;
    assert ((N - 1) / (2 * D + 1)) + 1 == 1;
    assert 1 <= N;
  } else {
    assert (N - 1) / (2 * D + 1) < N;
    assert ((N - 1) / (2 * D + 1)) + 1 <= N;
  }
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  var inspectors := ((N - 1) / (2 * D + 1)) + 1;
  return inspectors;
}
// </vc-code>

