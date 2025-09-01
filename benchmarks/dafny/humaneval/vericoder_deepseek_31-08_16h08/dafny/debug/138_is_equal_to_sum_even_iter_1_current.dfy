

// <vc-helpers>
lemma EvenSumExists(n: int)
  requires n >= 8 && n % 2 == 0
  ensures exists k1, k2, k3, k4 :: k1 >= 2 && k2 >= 2 && k3 >= 2 && k4 >= 2 && k1 + k2 + k3 + k4 == n
{
  // We can represent n as 2 + 2 + 2 + (n - 6)
  // Since n is even and >= 8, n - 6 >= 2 and n - 6 is even
  var k1 := 2;
  var k2 := 2;
  var k3 := 2;
  var k4 := n - 6;
  assert k1 >= 2 && k2 >= 2 && k3 >= 2 && k4 >= 2;
  assert k1 + k2 + k3 + k4 == n;
}

lemma NotEvenOrTooSmall(n: int)
  requires n < 8 || n % 2 != 0
  ensures !(exists k1, k2, k3, k4 :: k1 >= 2 && k2 >= 2 && k3 >= 2 && k4 >= 2 
           && k1 % 2 == 0 && k2 % 2 == 0 && k3 % 2 == 0 && k4 % 2 == 0
           && k1 + k2 + k3 + k4 == n)
{
  // If n < 8: The minimum sum of four even numbers >= 2 is 2+2+2+2=8
  // If n is odd: Sum of four even numbers is always even
}
// </vc-helpers>

// <vc-spec>
method is_equal_to_sum_even(n: int) returns (b : bool)
  // post-conditions-start
  ensures b <==> n % 2 == 0 && n >= 8 // 2 + 2 + 2 + (n - 6)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if n < 8 || n % 2 != 0 {
    return false;
  } else {
    assert n >= 8 && n % 2 == 0;
    // By EvenSumExists, we know there exist positive even numbers that sum to n
    return true;
  }
}
// </vc-code>

