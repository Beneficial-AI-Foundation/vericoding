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
lemma TriangularNumberIncreases(n: int)
  requires n >= 0
  ensures TriangularNumber(n + 1) > TriangularNumber(n)
{
  // TriangularNumber(n+1) = (n+1)*(n+2)/2
  // TriangularNumber(n) = n*(n+1)/2
  // Difference = (n+1)*(n+2)/2 - n*(n+1)/2 = (n+1)*((n+2) - n)/2 = (n+1)
  assert TriangularNumber(n + 1) - TriangularNumber(n) == n + 1;
}

lemma TriangularNumberMonotonic(a: int, b: int)
  requires 0 <= a < b
  ensures TriangularNumber(a) < TriangularNumber(b)
  decreases b - a
{
  if a + 1 == b {
    TriangularNumberIncreases(a);
  } else {
    TriangularNumberIncreases(a);
    TriangularNumberMonotonic(a + 1, b);
  }
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
  
  while TriangularNumber(t) < x
    invariant t >= 1
    invariant forall i :: 1 <= i < t ==> TriangularNumber(i) < x
  {
    t := t + 1;
  }
  
  result := t;
}
// </vc-code>

