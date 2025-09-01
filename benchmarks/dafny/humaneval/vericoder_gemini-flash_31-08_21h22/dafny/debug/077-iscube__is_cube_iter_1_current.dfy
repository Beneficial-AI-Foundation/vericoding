method cube_root(N: nat) returns (r: nat)
  // post-conditions-start
  ensures cube(r) <= N < cube(r + 1)
  ensures r <= N
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function cube(n: nat): nat { n * n * n }
// </vc-helpers>

// <vc-spec>
method is_cube(n: nat) returns (r: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r ==> exists r :: 0 <= r <= n && n == cube(r)
  ensures !r ==> forall r :: 0 <= r <= n ==> n != cube(r)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var low: nat := 0;
  var high: nat := N;
  var r_candidate: nat := 0;

  while low <= high
    invariant 0 <= low <= N + 1
    invariant 0 <= high <= N
    invariant r_candidate <= N
    invariant cube(r_candidate) <= N
    invariant low <= high + 1
    invariant (low == 0 || cube(low - 1) <= N)
    invariant (high == N || cube(high + 1) > N)
    invariant (low == 0 || cube(low - 1) <= N) // Ensure cube(r_candidate) <= N
  {
    var mid := low + (high - low) / 2;
    if cube(mid) <= N {
      r_candidate := mid;
      low := mid + 1;
    } else {
      high := mid - 1;
    }
  }
  return r_candidate;
}
// </vc-code>

function cube(n: int): int { n * n * n }
// pure-end