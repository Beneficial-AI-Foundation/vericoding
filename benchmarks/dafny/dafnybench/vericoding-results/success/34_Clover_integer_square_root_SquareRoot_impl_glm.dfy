

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SquareRoot(N:nat) returns (r:nat)
  ensures r*r <= N < (r+1)*(r+1)
// </vc-spec>
// <vc-code>
{
  var low := 0;
  var high := N;
  while low < high
    invariant 0 <= low <= high <= N
    invariant low * low <= N
    invariant (high+1)*(high+1) > N
  {
    var mid := (low + high + 1) / 2;
    if mid * mid <= N {
      low := mid;
    } else {
      high := mid - 1;
    }
  }
  return low;
}
// </vc-code>

