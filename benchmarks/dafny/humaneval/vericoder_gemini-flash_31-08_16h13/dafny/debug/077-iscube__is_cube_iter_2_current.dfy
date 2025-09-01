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
  var r_found: nat := 0;

  while low <= high
    invariant 0 <= low <= n + 1
    invariant 0 <= high <= n
    invariant cube(r_found) <= n
    invariant high < n + 1
    invariant r_found <= n
    invariant n < cube(low) || low == 0 || low == n + 1
    invariant cube(high + 1) > n || high == n
    invariant forall k: nat :: low <= k <= high ==> cube(k) > n || n < cube(k + 1)
    invariant (cube(r_found) <= n ) && (r_found == (low - 1) || high == (low - 1) ) ==> ( low == 0 || cube(low -1) <= n )
    invariant (low == 0 || r_found == low - 1) || (low == n + 1 || r_found == low - 1)
    invariant (high == n || r_found == high) || (high == 0 || r_found == high)

  {
    var mid: nat := (low + high) / 2;

    if n < cube(mid)
    {
      high := mid - 1;
    }
    else if cube(mid + 1) <= n
    {
      low := mid + 1;
    }
    else
    {
      r := (mid * mid * mid == n);
      return;
    }
  }

  r := (r_found * r_found * r_found == n);
}
// </vc-code>

function cube(n: int): int { n * n * n }
// pure-end