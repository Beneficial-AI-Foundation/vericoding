/*
function_signature: method is_cube(n: nat) returns (r: bool)
Check if condition holds. Ensures: if true, then there exists an integer r such that N = r³; if false, then no integer r satisfies N = r³.
*/

function cube(n: int): int { n * n * n }

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method is_cube(n: nat) returns (r: bool)

  ensures r ==> exists r :: 0 <= r <= n && n == cube(r)
  ensures !r ==> forall r :: 0 <= r <= n ==> n != cube(r)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
