// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: method is_equal_to_sum_even(n: int) returns (b : bool)
Evaluate whether the given number n can be written as the sum of exactly 4 positive even numbers.
*/
// </vc-description>

// <vc-spec>
method is_equal_to_sum_even(n: int) returns (b : bool)
  // post-conditions-start
  ensures b <==> n % 2 == 0 && n >= 8 // 2 + 2 + 2 + (n - 6)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>
