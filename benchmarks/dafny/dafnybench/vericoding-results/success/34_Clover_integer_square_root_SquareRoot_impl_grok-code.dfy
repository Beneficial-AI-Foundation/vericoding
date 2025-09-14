

// <vc-helpers>
// No helpers needed for this fix
// </vc-helpers>

// <vc-spec>
method SquareRoot(N:nat) returns (r:nat)
  ensures r*r <= N < (r+1)*(r+1)
// </vc-spec>
// <vc-code>
{
  var lo: int := 0;
  var hi: int := N + 1;
  while lo < hi
    invariant 0 <= lo <= hi <= N + 1
    invariant forall k: nat :: 0 <= k < lo ==> k * k <= N
    invariant forall k: nat :: hi <= k ==> k * k > N
  {
    var mid: int := (lo + hi) / 2;
    if mid * mid <= N {
      lo := mid + 1;
    } else {
      hi := mid;
    }
  }
  if lo == 0 {
    r := 0;
  } else {
    r := lo - 1;
  }
}
// </vc-code>

