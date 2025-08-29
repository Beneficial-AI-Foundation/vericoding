// <vc-helpers>
predicate is_positive_even(x: int)
{
  x > 0 && x % 2 == 0
}

ghost predicate can_be_sum_of_four_positive_evens(n: int)
{
  exists a, b, c, d :: is_positive_even(a) && is_positive_even(b) && is_positive_even(c) && is_positive_even(d) && a + b + c + d == n
}

lemma sum_four_positive_evens_bound(n: int)
  requires can_be_sum_of_four_positive_evens(n)
  ensures n >= 8
{
  var a, b, c, d :| is_positive_even(a) && is_positive_even(b) && is_positive_even(c) && is_positive_even(d) && a + b + c + d == n;
  assert a >= 2 && b >= 2 && c >= 2 && d >= 2;
}

lemma eight_is_sum_of_four_positive_evens()
  ensures can_be_sum_of_four_positive_evens(8)
{
  assert is_positive_even(2) && is_positive_even(2) && is_positive_even(2) && is_positive_even(2);
  assert 2 + 2 + 2 + 2 == 8;
}

lemma if_n_works_then_n_plus_2_works(n: int)
  requires can_be_sum_of_four_positive_evens(n)
  ensures can_be_sum_of_four_positive_evens(n + 2)
{
  var a, b, c, d :| is_positive_even(a) && is_positive_even(b) && is_positive_even(c) && is_positive_even(d) && a + b + c + d == n;
  assert is_positive_even(a + 2) && is_positive_even(b) && is_positive_even(c) && is_positive_even(d);
  assert (a + 2) + b + c + d == n + 2;
}

lemma all_even_ge_8_can_be_sum()
  ensures forall n :: n >= 8 && n % 2 == 0 ==> can_be_sum_of_four_positive_evens(n)
{
  forall n | n >= 8 && n % 2 == 0
    ensures can_be_sum_of_four_positive_evens(n)
  {
    eight_is_sum_of_four_positive_evens();
    var k := 8;
    while k < n
      invariant k >= 8 && k <= n
      invariant k % 2 == 0
      invariant can_be_sum_of_four_positive_evens(k)
    {
      if_n_works_then_n_plus_2_works(k);
      k := k + 2;
    }
  }
}

lemma odd_or_small_cannot_be_sum(n: int)
  ensures (n % 2 == 1 || n < 8) ==> !can_be_sum_of_four_positive_evens(n)
{
  if can_be_sum_of_four_positive_evens(n) {
    sum_four_positive_evens_bound(n);
    var a, b, c, d :| is_positive_even(a) && is_positive_even(b) && is_positive_even(c) && is_positive_even(d) && a + b + c + d == n;
    assert n % 2 == 0;
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
method is_equal_to_sum_even(n: int) returns (b: bool)
  ensures b <==> can_be_sum_of_four_positive_evens(n)
// </vc-spec>
// <vc-code>
method is_equal_to_sum_even(n: int) returns (b: bool)
  ensures b <==> can_be_sum_of_four_positive_evens(n)
{
  if n < 8 {
    odd_or_small_cannot_be_sum(n);
    b := false;
    return;
  }
  
  if n % 2 == 1 {
    odd_or_small_cannot_be_sum(n);
    b := false;
    return;
  }
  
  all_even_ge_8_can_be_sum();
  b := true;
}
// </vc-code>
