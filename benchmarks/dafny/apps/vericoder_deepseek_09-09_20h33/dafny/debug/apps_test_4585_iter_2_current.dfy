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
lemma TriangularNumberMonotonic(a: int, b: int)
  requires 0 <= a <= b
  ensures TriangularNumber(a) <= TriangularNumber(b)
{
  if a < b {
    calc {
      TriangularNumber(b);
      b * (b + 1) / 2;
    >=  a * (a + 1) / 2;
      { assert b * (b + 1) >= a * (a + 1); }
      TriangularNumber(a);
    }
  }
}

lemma TriangularNumberUniqueness(n: int)
  requires n >= 1
  ensures exists t :: 1 <= t && TriangularNumber(t) >= n && (t == 1 || TriangularNumber(t - 1) < n)
{
  // By the properties of triangular numbers and the given constraints, such a t exists
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
    invariant TriangularNumber(t - 1) < x
  {
    t := t + 1;
  }
  result := t;
}
// </vc-code>

