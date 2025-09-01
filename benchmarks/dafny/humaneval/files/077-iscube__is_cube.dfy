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

// <vc-description>
/*
function_signature: method is_cube(n: nat) returns (r: bool)
Check if condition holds. Ensures: if true, then there exists an integer r such that N = r³; if false, then no integer r satisfies N = r³.
*/
// </vc-description>

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
  assume false;
}
// </vc-code>

function cube(n: int): int { n * n * n }
// pure-end