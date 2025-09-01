method cube_root(N: nat) returns (r: nat)
  // post-conditions-start
  ensures cube(r) <= N < cube(r + 1)
  ensures r <= N
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function cube_nat(n: nat): nat { n * n * n }
function cube_int(n: int): int { n * n * n }
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
    invariant cube_nat(r_candidate) <= n
    invariant low <= high + 1
    invariant (low == 0 || cube_nat(low - 1) <= n)
    invariant high == n || high == n + 1 || (high < n && cube_nat(high + 1) > n) || (high == 0 && n==0)
    invariant high >= 0
    invariant high == n || high + 1 == n || (high < n && (high + 1 > n || cube_nat(high + 1) > n))
    invariant forall r' :: low <= r' ==> cube_nat(r') > n || r' > n
    invariant forall r' :: r' <= high ==> cube_nat(r') <= n || (r' == n && cube_nat(r') == n) || (r' < n && cube_nat(r') < n)
  {
    var mid_candidate := low + (high - low) / 2;
    var mid := mid_candidate; 

    if cube_nat(mid) <= n {
      r_candidate := mid;
      low := mid + 1;
    } else {
      high := mid - 1;
    }
  }
  return cube_nat(r_candidate) == n;
}
// </vc-code>

function cube(n: int): int { n * n * n }
// pure-end