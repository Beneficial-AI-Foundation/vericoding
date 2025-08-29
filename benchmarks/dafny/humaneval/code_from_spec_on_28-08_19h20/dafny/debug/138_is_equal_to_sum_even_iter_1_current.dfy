// <vc-helpers>
lemma FourEvenSumBounds(n: int)
  requires n >= 8
  ensures n == 8 || (n - 8) % 2 == 0
{
  if n == 8 {
    // Base case: 8 = 2 + 2 + 2 + 2
  } else {
    // For n > 8, we need (n - 8) to be even
    // This is because we can write n = 2 + 2 + 2 + 2 + k where k = n - 8
    // and we need to distribute k evenly among the four numbers
  }
}

lemma EvenSumParity(a: int, b: int, c: int, d: int)
  requires a > 0 && a % 2 == 0
  requires b > 0 && b % 2 == 0  
  requires c > 0 && c % 2 == 0
  requires d > 0 && d % 2 == 0
  ensures (a + b + c + d) % 2 == 0
{
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
  ensures b <==> (exists a, c, e, g :: a > 0 && a % 2 == 0 && 
                                      c > 0 && c % 2 == 0 && 
                                      e > 0 && e % 2 == 0 && 
                                      g > 0 && g % 2 == 0 && 
                                      a + c + e + g == n)
// </vc-spec>
// <vc-code>
method is_equal_to_sum_even(n: int) returns (b: bool)
  ensures b <==> (exists a, c, e, g :: a > 0 && a % 2 == 0 && 
                                      c > 0 && c % 2 == 0 && 
                                      e > 0 && e % 2 == 0 && 
                                      g > 0 && g % 2 == 0 && 
                                      a + c + e + g == n)
{
  if n < 8 {
    b := false;
  } else if n % 2 != 0 {
    b := false;
  } else {
    b := true;
    FourEvenSumBounds(n);
  }
}
// </vc-code>
