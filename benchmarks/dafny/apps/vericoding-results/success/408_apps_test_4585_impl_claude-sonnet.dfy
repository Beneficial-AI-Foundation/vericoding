predicate ValidInput(x: int)
{
  x >= 1
}

function TriangularNumber(n: int): int
  requires n >= 0
{
  n * (n + 1) / 2
}

predicate IsMinimalTime(t: int, x: int)
  requires x >= 1
{
  t >= 1 && 
  TriangularNumber(t) >= x &&
  (t == 1 || TriangularNumber(t - 1) < x)
}

// <vc-helpers>
lemma TriangularIncreasing(n: int)
  requires n >= 0
  ensures TriangularNumber(n + 1) > TriangularNumber(n)
{
  assert TriangularNumber(n + 1) == (n + 1) * (n + 2) / 2;
  assert TriangularNumber(n) == n * (n + 1) / 2;
  assert TriangularNumber(n + 1) - TriangularNumber(n) == (n + 1) * (n + 2) / 2 - n * (n + 1) / 2;
  assert TriangularNumber(n + 1) - TriangularNumber(n) == (n + 1) * ((n + 2) - n) / 2;
  assert TriangularNumber(n + 1) - TriangularNumber(n) == (n + 1) * 2 / 2;
  assert TriangularNumber(n + 1) - TriangularNumber(n) == (n + 1);
  assert n + 1 > 0;
}

lemma TriangularPositive(n: int)
  requires n >= 1
  ensures TriangularNumber(n) >= 1
{
  assert TriangularNumber(n) == n * (n + 1) / 2;
  assert n >= 1 && n + 1 >= 2;
  assert n * (n + 1) >= 2;
}
// </vc-helpers>

// <vc-spec>
method solve(x: int) returns (result: int)
  requires ValidInput(x)
  ensures IsMinimalTime(result, x)
// </vc-spec>
// <vc-code>
{
  result := 1;
  
  while TriangularNumber(result) < x
    invariant result >= 1
    invariant TriangularNumber(result - 1) < x || result == 1
    decreases x - TriangularNumber(result)
  {
    TriangularIncreasing(result);
    result := result + 1;
  }
  
  if result > 1 {
    TriangularIncreasing(result - 2);
  }
}
// </vc-code>

