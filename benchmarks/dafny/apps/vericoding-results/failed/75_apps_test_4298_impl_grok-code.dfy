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
// Helper lemma to ensure the number of inspectors is within bounds
lemma InspectorsBounds(N: int, D: int)
  requires ValidInput(N, D)
  ensures var inspectors := ((N - 1) / (2 * D + 1)) + 1;
          inspectors >= 1 && inspectors <= N
{
  // Prove inspectors >= 1
  var num := ((N - 1) / (2 * D + 1));
  assert num >= 0;
  var inspectors := num + 1;
  assert inspectors >= 1;

  // Prove inspectors <= N
  calc {
    num <= (N - 1) / 1;
    == true;
  }
  assert inspectors <= N;
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
var inspectors := ((N - 1) / (2 * D + 1)) + 1;
InspectorsBounds(N, D);
return inspectors;
// </vc-code>

