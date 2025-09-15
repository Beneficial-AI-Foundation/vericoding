// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method is_equal_to_sum_even(n: int) returns (b : bool)

  ensures b <==> n % 2 == 0 && n >= 8
// </vc-spec>
// <vc-code>
{
  b := (n % 2 == 0) && (n >= 8);
}
// </vc-code>
