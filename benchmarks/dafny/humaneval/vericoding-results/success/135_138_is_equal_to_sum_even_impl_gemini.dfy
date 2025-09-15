// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsSpecificEven(k: int) { k % 2 == 0 && k >= 8 }
// </vc-helpers>

// <vc-spec>
method is_equal_to_sum_even(n: int) returns (b : bool)

  ensures b <==> n % 2 == 0 && n >= 8
// </vc-spec>
// <vc-code>
{
  b := IsSpecificEven(n);
}
// </vc-code>
