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
  var high: nat := n;
  var r_candidate: nat := 0;

  while low <= high
    invariant 0 <= low <= n + 1
    invariant 0 <= high <= n || (high == 0 && n == 0) // if n is 0, high can be 0.
    invariant r_candidate <= n
    invariant cube(r_candidate) <= n
    invariant low <= high + 1
    invariant (low == 0 || cube(low - 1) <= n)
    invariant high == n || high == n + 1 || cube(high + 1) > n // high can be n+1 if n is 0
    invariant high >= 0
  {
    var mid_candidate := low + (high - low) / 2;
    var mid := mid_candidate; 

    if cube(mid) <= n {
      r_candidate := mid;
      low := mid + 1;
    } else {
      high := mid - 1;
    }
  }
  return cube(r_candidate) == n;
}
// </vc-code>

function cube(n: int): int { n * n * n }
// pure-end