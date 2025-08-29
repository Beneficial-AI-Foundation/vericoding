// <vc-helpers>
lemma CanDecomposeIfAtLeastEight(n: int)
  requires n >= 8
  ensures exists a, c, d, e :: a > 0 && c > 0 && d > 0 && e > 0 && a % 2 == 0 && c % 2 == 0 && d % 2 == 0 && e % 2 == 0 && a + c + d + e == n
{
  var remainder := n - 6;
  assert remainder >= 2;
  assert remainder % 2 == n % 2;
  if remainder % 2 == 0 {
    assert remainder > 0 && remainder % 2 == 0;
    assert 2 > 0 && 2 % 2 == 0;
    assert 2 + 2 + 2 + remainder == n;
  } else {
    var adj_remainder := remainder + 2;
    assert adj_remainder >= 4;
    assert adj_remainder % 2 == 0;
    assert adj_remainder > 0 && adj_remainder % 2 == 0;
    assert 2 > 0 && 2 % 2 == 0;
    assert 2 + 2 + 4 + (adj_remainder - 2) == n;
  }
}

lemma CannotDecomposeIfLessThanEight(n: int)
  requires n < 8
  ensures !exists a, c, d, e :: a > 0 && c > 0 && d > 0 && e > 0 && a % 2 == 0 && c % 2 == 0 && d % 2 == 0 && e % 2 == 0 && a + c + d + e == n
{
  if exists a, c, d, e :: a > 0 && c > 0 && d > 0 && e > 0 && a % 2 == 0 && c % 2 == 0 && d % 2 == 0 && e % 2 == 0 && a + c + d + e == n {
    var a, c, d, e :| a > 0 && c > 0 && d > 0 && e > 0 && a % 2 == 0 && c % 2 == 0 && d % 2 == 0 && e % 2 == 0 && a + c + d + e == n;
    assert a >= 2 && c >= 2 && d >= 2 && e >= 2;
    assert a + c + d + e >= 8;
    assert n >= 8;
    assert false;
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method is_equal_to_sum_even(n: int) returns (b : bool)
Evaluate whether the given number n can be written as the sum of exactly 4 positive even numbers.
*/
// </vc-description>

// <vc-spec>
method is_equal_to_sum_even(n: int) returns (b : bool)
  ensures b <==> exists a, c, d, e :: a > 0 && c > 0 && d > 0 && e > 0 && a % 2 == 0 && c % 2 == 0 && d % 2 == 0 && e % 2 == 0 && a + c + d + e == n
// </vc-spec>
// <vc-code>
method is_equal_to_sum_even(n: int) returns (b : bool)
  ensures b <==> exists a, c, d, e :: a > 0 && c > 0 && d > 0 && e > 0 && a % 2 == 0 && c % 2 == 0 && d % 2 == 0 && e % 2 == 0 && a + c + d + e == n
{
  if n < 8 {
    CannotDecomposeIfLessThanEight(n);
    b := false;
  } else {
    CanDecomposeIfAtLeastEight(n);
    b := true;
  }
}
// </vc-code>
