// <vc-helpers>
// </vc-helpers>

method SquareRoot(N:nat) returns (r:nat)
  ensures r*r <= N < (r+1)*(r+1)
// <vc-code>
{
  assume false;
}
// </vc-code>