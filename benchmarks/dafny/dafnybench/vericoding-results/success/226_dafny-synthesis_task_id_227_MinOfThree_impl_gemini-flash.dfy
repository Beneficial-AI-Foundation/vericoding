

// <vc-helpers>
lemma MinOrdering(f1: int, f2: int, f3: int, m: int)
  requires m <= f1 && m <= f2 && m <= f3
  requires m == f1 || m == f2 || m == f3
  ensures m == Min(f1, Min(f2, f3))
{
  if m == f1 {
    assert Min(f2, f3) >= m;
    assert Min(f1, Min(f2, f3)) == m;
  } else if m == f2 {
    assert Min(f1, Min(f2, f3)) == Min(f1, m);
    assert Min(f1, m) == m;
  } else { // m == f3
    assert Min(f1, Min(f2, f3)) == Min(f1, Min(f2, m));
		assert Min(f2, m) == m;
    assert Min(f1, m) == m;
  }
}

function Min(x: int, y: int): int
  ensures (Min(x,y) == x || Min(x,y) == y) && (Min(x,y) <= x && Min(x,y) <= y)
{
  if x <= y then x else y
}
// </vc-helpers>

// <vc-spec>
method MinOfThree(a: int, b: int, c: int) returns (min: int)
    ensures min <= a && min <= b && min <= c
    ensures (min == a) || (min == b) || (min == c)
// </vc-spec>
// <vc-code>
{
  min := Min(a, Min(b, c));
}
// </vc-code>

