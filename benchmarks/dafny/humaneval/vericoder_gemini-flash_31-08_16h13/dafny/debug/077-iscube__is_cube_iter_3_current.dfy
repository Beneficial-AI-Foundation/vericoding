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

  while low <= high
    invariant 0 <= low <= n + 1
    invariant 0 <= high <= n
    invariant cube_nat(low) > n || n < cube_nat(high + 1) || high < low
    invariant (low == 0 || cube_nat(low - 1) <= n)
    invariant (high == n || cube_nat(high + 1) > n)
    invariant forall k: nat :: (k < low || k > high) ==> (cube_nat(k) > n || cube_nat(k) < n)
  {
    var mid: nat := (low + high) / 2;

    if cube_nat(mid) == n
    {
      r := true;
      return;
    }
    else if cube_nat(mid) > n
    {
      high := mid - 1;
    }
    else // cube_nat(mid) < n
    {
      low := mid + 1;
    }
  }

  r := false;
}
// </vc-code>

function cube(n: int): int { n * n * n }
// pure-end