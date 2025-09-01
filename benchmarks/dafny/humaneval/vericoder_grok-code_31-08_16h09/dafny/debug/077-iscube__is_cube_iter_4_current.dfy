method cube_root(N: nat) returns (r: nat)
  // post-conditions-start
  ensures cube(r) <= N < cube(r + 1)
  ensures r <= N
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>

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
  var r_nat := 0;
  while r_nat * r_nat * r_nat < n {
    r_nat := r_nat + 1;
  }
  r := r_nat * r_nat * r_nat == n;
}
// </vc-code>

function cube(n: int): int { n * n * n }
// pure-end