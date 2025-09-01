

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method cube_root(N: nat) returns (r: nat)
  // post-conditions-start
  ensures cube(r) <= N < cube(r + 1)
  ensures r <= N
  // post-conditions-end
// </vc-spec>
// <vc-code>
var low, high := 0, N + 1;
  while low < high
    invariant 0 <= low <= high <= N + 1
    invariant low == 0 || cube(low - 1) <= N
    invariant high == N + 1 || cube(high) > N
  {
    var mid := (low + high) / 2;
    if cube(mid) <= N {
      low := mid + 1;
    } else {
      high := mid;
    }
  }
  return low - 1;
// </vc-code>

method is_cube(n: nat) returns (r: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r ==> exists r :: 0 <= r <= n && n == cube(r)
  ensures !r ==> forall r :: 0 <= r <= n ==> n != cube(r)
  // post-conditions-end
{
  assume{:axiom} false;
}
function cube(n: int): int { n * n * n }
// pure-end