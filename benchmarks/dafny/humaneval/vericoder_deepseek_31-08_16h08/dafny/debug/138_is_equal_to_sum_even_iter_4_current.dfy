

// <vc-helpers>
lemma EvenSumExists(n: int)
  requires n >= 8 && n % 2 == 0
  ensures exists k1, k2, k3, k4 :: k1 >= 2 && k2 >= 2 && k3 >= 2 && k4 >= 2 && k1 + k2 + k3 + k4 == n
{
  var k1 := 2;
  var k2 := 2;
  var k3 := 2;
  var k4 := n - 6;
  assert k1 >= 2 && k2 >= 2 && k3 >= 2 && k4 >= 2;
  assert k1 + k2 + k3 + k4 == n;
}

lemma NotEvenOrTooSmall(n: int)
  requires n < 8 || n % 2 != 0
  ensures !(exists k1, k2, k3, k4 :: k1 >= 2 && k2 >= 2 && k3 >= 2 && k4 >= 2 && k1 + k2 + k3 + k4 == n)
{
  if n < 8 {
    // Minimum sum of four numbers >= 2 is 2+2+2+2=8
    assert forall k1, k2, k3, k4 :: k1 >= 2 && k2 >= 2 && k3 >= 2 && k4 >= 2 ==> k1 + k2 + k3 + k4 >= 8;
  } else if n % 2 != 0 {
    // Sum of four even numbers is always even, but we need general case
    assert forall k1, k2, k3, k4 :: k1 >= 2 && k2 >= 2 && k3 >= 2 && k4 >= 2 ==> (k1 + k2 + k3 + k4) % 2 == (k1 % 2 + k2 % 2 + k3 % 2 + k4 % 2) % 2;
  }
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
    NotEvenOrTooSmall(n);
    b := false;
  } else {
    EvenSumExists(n);
    b := true;
  }
}
// </vc-code>

