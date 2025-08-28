// <vc-helpers>
lemma SquarePreservesOrder(a: nat, b: nat)
  requires a <= b
  ensures a * a <= b * b
{
  if a == 0 {
  } else if a == b {
  } else {
    assert a < b;
    assert a * a + a * (b - a) == a * b;
    assert a * b + (b - a) * b == b * b;
    assert a * (b - a) >= 0;
    assert (b - a) * b >= 0;
    assert a * a <= a * b <= b * b;
  }
}

lemma SquareGrowth(r: nat, N: nat)
  requires r * r <= N
  requires N < (r + 1) * (r + 1)
  ensures r * r <= N < (r + 1) * (r + 1)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method SquareRoot(N:nat) returns (r:nat)
  ensures r*r <= N < (r+1)*(r+1)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  r := 0;
  while (r + 1) * (r + 1) <= N
    invariant r * r <= N
    decreases N - r * r
  {
    r := r + 1;
  }
}
// </vc-code>
