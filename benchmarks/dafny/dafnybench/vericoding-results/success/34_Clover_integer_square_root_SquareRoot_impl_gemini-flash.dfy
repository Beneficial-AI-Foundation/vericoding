

// <vc-helpers>
function Square(x: nat): nat {
  x * x
}
// </vc-helpers>

// <vc-spec>
method SquareRoot(N:nat) returns (r:nat)
  ensures r*r <= N < (r+1)*(r+1)
// </vc-spec>
// <vc-code>
{
  var current_r := 0; // Renamed 'r' to 'current_r' to avoid duplicate variable name with the return parameter 'r'
  while Square(current_r + 1) <= N
    invariant current_r * current_r <= N
    decreases N - current_r * current_r
  {
    current_r := current_r + 1;
  }
  return current_r;
}
// </vc-code>

