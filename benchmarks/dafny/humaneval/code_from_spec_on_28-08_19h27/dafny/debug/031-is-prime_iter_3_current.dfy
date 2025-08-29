// <vc-helpers>
predicate IsDivisibleBy(n: int, d: int)
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

lemma SquareRootProperty(n: int, d: int)
  requires n > 1 && d > 1 && n % d == 0
  ensures d <= n / d
  ensures d * d <= n || n / d < d
{
}

lemma PrimalityHelper(n: int, limit: int)
  requires n > 2 && n % 2 != 0 && limit * limit <= n
  requires forall d :: 2 <= d <= limit ==> n % d != 0
  ensures forall d :: limit < d < n && d * d <= n ==> n % d != 0
{
  forall d | limit < d < n && d * d <= n
    ensures n % d != 0
  {
    if n % d == 0 {
      assert d <= n / d;
      assert n / d < d;
      assert false;
    }
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def is_prime(n)
Return true if a given number is prime, and false otherwise.
*/
// </vc-description>

// <vc-spec>
function is_prime(n: int): bool
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
    var found_divisor := false;
    while i * i <= n && !found_divisor
      invariant i >= 3
      invariant i % 2 == 1
      invariant !found_divisor ==> forall d :: 2 <= d < i ==> n % d != 0
      invariant found_divisor ==> exists d :: 2 <= d < i && n % d == 0
      decreases n - i * i
    {
      if n % i == 0 {
        found_divisor := true;
      } else {
        i := i + 2;
      }
    }
    if found_divisor then
      false
    else
      PrimalityHelper(n, i - 2);
      true
}
// </vc-code>
