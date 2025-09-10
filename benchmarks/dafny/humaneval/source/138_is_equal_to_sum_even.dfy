method is_equal_to_sum_even(n: int) returns (b : bool)
  // post-conditions-start
  ensures b <==> n % 2 == 0 && n >= 8 // 2 + 2 + 2 + (n - 6)
  // post-conditions-end
{
  // impl-start
  b := n % 2 == 0 && n >= 8;
  // impl-end
}
