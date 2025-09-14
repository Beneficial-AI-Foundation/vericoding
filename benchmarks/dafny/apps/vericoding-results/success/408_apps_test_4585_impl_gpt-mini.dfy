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
lemma TriangularNumber_monotone(n: int)
  requires n >= 0
  ensures TriangularNumber(n+1) > TriangularNumber(n)
{
  // Unfold the definition of TriangularNumber
  assert TriangularNumber(n+1) == (n+1)*(n+2)/2;
  assert TriangularNumber(n) == n*(n+1)/2;

  // Compute the numerator difference
  assert ((n+1)*(n+2) - n*(n+1)) == 2*(n+1);

  // Relate the difference to n+1
  assert TriangularNumber(n+1) - TriangularNumber(n) ==
         ((n+1)*(n+2) - n*(n+1)) / 2;
  assert TriangularNumber(n+1) - TriangularNumber(n) == (2*(n+1))/2;
  assert (2*(n+1))/2 == n+1;

  assert TriangularNumber(n+1) - TriangularNumber(n) == n+1;
  assert n+1 > 0;
}
// </vc-helpers>

// <vc-spec>
method solve(x: int) returns (result: int)
  requires ValidInput(x)
  ensures IsMinimalTime(result, x)
// </vc-spec>
// <vc-code>
{
  var t := 1;
  assert t >= 1;
  // establish the loop invariant initially
  assert TriangularNumber(t-1) < x;
  while TriangularNumber(t) < x
    invariant t >= 1
    invariant TriangularNumber(t-1) < x
    decreases x - TriangularNumber(t-1)
  {
    TriangularNumber_monotone(t-1);
    t := t + 1;
  }
  result := t;
}
// </vc-code>

