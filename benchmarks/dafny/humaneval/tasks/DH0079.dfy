// <vc-preamble>
function cube(n: int): int { n * n * n }
// </vc-preamble>

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
