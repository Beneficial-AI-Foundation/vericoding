

// <vc-helpers>

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
  {
    r := r + 1;
  }
}
// </vc-code>

