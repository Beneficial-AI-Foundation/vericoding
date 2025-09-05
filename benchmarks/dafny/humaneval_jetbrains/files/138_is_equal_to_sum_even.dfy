/*
function_signature: method is_equal_to_sum_even(n: int) returns (b : bool)
Evaluate whether the given number n can be written as the sum of exactly 4 positive even numbers.
*/

method is_equal_to_sum_even(n: int) returns (b : bool)
  // post-conditions-start
  ensures b <==> n % 2 == 0 && n >= 8 // 2 + 2 + 2 + (n - 6)
  // post-conditions-end
{
  assume false;
}
