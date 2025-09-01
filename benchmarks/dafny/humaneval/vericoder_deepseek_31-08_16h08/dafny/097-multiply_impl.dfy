function last_digit(n: int): int
  // post-conditions-start
  ensures n >= 0 ==> last_digit(n) == n % 10
  ensures n < 0 ==> last_digit(n) == (-n) % 10
  // post-conditions-end
{
  // impl-start
  if n < 0 then (-n) % 10 else n % 10
  // impl-end
}

// <vc-helpers>
lemma LastDigitLemma(n: int)
  requires n >= 0
  ensures n % 10 == last_digit(n)
{
  // The function definition already ensures this
}

lemma LastDigitNegativeLemma(n: int)
  requires n < 0
  ensures (-n) % 10 == last_digit(n)
{
  // The function definition already ensures this
}
// </vc-helpers>

// <vc-spec>
method multiply(a: int, b: int) returns (c: int)
  // pre-conditions-start
  requires a >= 0
  requires b >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures c == last_digit(a) * last_digit(b)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var lastA := if a == 0 then 0 else a % 10;
  var lastB := if b == 0 then 0 else b % 10;
  
  assert lastA == last_digit(a);
  assert lastB == last_digit(b);
  
  c := lastA * lastB;
}
// </vc-code>

