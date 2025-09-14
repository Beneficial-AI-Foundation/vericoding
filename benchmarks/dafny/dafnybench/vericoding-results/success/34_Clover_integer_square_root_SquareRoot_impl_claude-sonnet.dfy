

// <vc-helpers>
lemma SquareRootProperties(r: nat, N: nat)
  requires r * r <= N
  requires N < (r + 1) * (r + 1)
  ensures r * r <= N < (r + 1) * (r + 1)
{
}

lemma MonotonicityLemma(i: nat, j: nat)
  requires i <= j
  ensures i * i <= j * j
{
}

lemma SquareGrowthLemma(r: nat)
  ensures r * r < (r + 1) * (r + 1)
{
  calc {
    (r + 1) * (r + 1);
    ==
    r * r + 2 * r + 1;
    >
    r * r;
  }
}
// </vc-helpers>

// <vc-spec>
method SquareRoot(N:nat) returns (r:nat)
  ensures r*r <= N < (r+1)*(r+1)
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

