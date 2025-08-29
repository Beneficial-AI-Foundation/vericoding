// <vc-helpers>
predicate method IsDivisibleBy(n: int, d: int)
  requires d > 0
{
  n % d == 0
}

predicate HasDivisorInRange(n: int, lower: int, upper: int)
  requires lower >= 2
  requires upper >= lower
  decreases upper - lower + 1
{
  if lower > upper then false
  else if n % lower == 0 then true
  else HasDivisorInRange(n, lower + 1, upper)
}

lemma DivisorProperties(n: int, d: int)
  requires n > 1 && d > 1 && n % d == 0
  ensures d <= n
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def is_prime(n)
Return true if a given number is prime, and false otherwise.
*/
// </vc-description>

// <vc-spec>
predicate method is_prime(n: int)
  ensures is_prime(n) <==> (n > 1 && forall d :: 2 <= d < n ==> n % d != 0)
// </vc-spec>
// <vc-code>
{
  if n <= 1 then
    false
  else if n == 2 then
    true
  else if n % 2 == 0 then
    false
  else
    var i := 3;
    while i * i <= n
      invariant i >= 3
      invariant i % 2 == 1
      invariant forall d :: 2 <= d < i ==> n % d != 0
    {
      if n % i == 0 {
        return false;
      }
      i := i + 2;
    }
    true
}
// </vc-code>
