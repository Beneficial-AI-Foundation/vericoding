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
lemma LemmaCoverage(N: int, D: int)
  requires ValidInput(N, D)
  ensures TreesCovered(N, D, ((N - 1) / (2 * D + 1)) + 1)
{
}

lemma LemmaMinimumInspectors(N: int, D: int) returns (k: int)
  requires ValidInput(N, D)
  ensures TreesCovered(N, D, k)
  ensures forall k' :: k' < k ==> !TreesCovered(N, D, k')
{
  k := ((N - 1) / (2 * D + 1)) + 1;
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  var k := ((N - 1) / (2 * D + 1)) + 1;
  return k;
}
// </vc-code>

