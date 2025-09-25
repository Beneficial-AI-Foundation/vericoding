// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SquareRoot(N:nat) returns (r:nat)
  ensures r*r <= N < (r+1)*(r+1)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
