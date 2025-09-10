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
  // Prove inspectors >=1
  var num := ((N - 1) / (2 * D + 1));
  var inspectors := num + 1;
  assert inspectors >=1;

  // Prove inspectors <= N
  var dens := 2 * D + 1;
  assert dens >= 3;
  var upper := (N -1);
  assert num == upper / dens;
  assert upper / dens <= upper / 3 <= upper;  // Mait since dens >=3, upper / dens <= upper /3 <= upper
  assert inspectors == num +1;
  assert num <= upper;
  assert inspectors <= upper +1;
  assert upper +1 <= N;  // since upper = N-1
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
method CalculateInspectors(N: int, D: int) returns (result: int)
  requires ValidInput(N, D)
  ensures TreesCovered(N, D, result)
{
  var inspectors := ((N - 1) / (2 * D + 1)) + 1;
  InspectorsBounds(N, D);
  result := inspectors;
}
// </vc-code>

