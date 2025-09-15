

// <vc-helpers>
// No helpers needed for this proof.
// </vc-helpers>

// <vc-spec>
method is_equal_to_sum_even(n: int) returns (b : bool)
  // post-conditions-start
  ensures b <==> n % 2 == 0 && n >= 8 // 2 + 2 + 2 + (n - 6)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  b := n >= 8 && n % 2 == 0;
}
// </vc-code>

