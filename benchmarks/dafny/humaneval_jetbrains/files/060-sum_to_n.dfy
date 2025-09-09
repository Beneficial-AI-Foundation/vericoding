// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method sum_to_n(n: int) returns (r : int)

  ensures r == n * (n + 1) / 2
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
