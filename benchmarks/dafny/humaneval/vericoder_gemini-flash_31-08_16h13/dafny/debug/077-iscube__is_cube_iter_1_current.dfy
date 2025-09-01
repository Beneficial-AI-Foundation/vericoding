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
  var r_found: nat := 0;

  while low <= high
    invariant 0 <= low <= N + 1
    invariant 0 <= high <= N
    invariant cube(r_found) <= N
    invariant high < N + 1 // Add this invariant
    invariant r_found <= N // Add this invariant
    invariant N < cube(low) || low == 0 || low == N + 1 // Add this invariant
    invariant cube(high + 1) > N || high == N // Add this invariant
    invariant forall k: nat :: low <= k <= high ==> cube(k) > N || N < cube(k + 1) // Add this invariant
    invariant (cube(r_found) <= N ) && (r_found == (low - 1) || high == (low - 1) ) ==> ( low == 0 || cube(low -1) <= N ) // Add this invariant
    invariant (low == 0 || r_found == low - 1) || (low == N + 1 || r_found == low - 1)
    invariant (high == N || r_found == high) || (high == 0 || r_found == high)

  {
    var mid: nat := (low + high) / 2;

    if N < cube(mid)
    {
      high := mid - 1;
    }
    else if cube(mid + 1) <= N
    {
      low := mid + 1;
    }
    else
    {
      r := mid;
      return;
    }
  }

  r := r_found;
}
// </vc-code>

function cube(n: int): int { n * n * n }
// pure-end