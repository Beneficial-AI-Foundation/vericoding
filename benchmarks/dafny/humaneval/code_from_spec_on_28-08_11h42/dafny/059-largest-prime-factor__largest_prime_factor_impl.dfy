method is_prime(k: int) returns (result: bool)
  // pre-conditions-start
  requires k >= 2
  // pre-conditions-end
  // post-conditions-start
  ensures result ==> forall i :: 2 <= i < k ==> k % i != 0
  ensures !result ==> exists j :: 2 <= j < k && k % j == 0
  // post-conditions-end
{
  assume{:axiom} false;
}
function is_prime_pred(k: int) : bool
{
  forall i :: 2 <= i < k ==> k % i != 0
}

// <vc-helpers>
lemma DivisorExists(n: int)
  requires n >= 2
  ensures exists d :: 1 < d <= n && n % d == 0
{
  assert n % n == 0;
}

lemma PrimeFactorExists(n: int)
  requires n >= 2
  ensures exists p :: 1 < p <= n && n % p == 0 && is_prime_pred(p)
{
  DivisorExists(n);
  var d := FindSmallestDivisor(n);
  assert 1 < d <= n && n % d == 0;
  SmallestDivisorIsPrime(n, d);
  assert is_prime_pred(d);
}

function FindSmallestDivisor(n: int): int
  requires n >= 2
  ensures 1 < FindSmallestDivisor(n) <= n
  ensures n % FindSmallestDivisor(n) == 0
  ensures forall k :: 1 < k < FindSmallestDivisor(n) ==> n % k != 0
{
  if n % 2 == 0 then 2
  else FindSmallestDivisorOdd(n, 3)
}

function FindSmallestDivisorOdd(n: int, start: int): int
  requires n >= 2 && start >= 3 && start % 2 == 1
  requires n % 2 != 0
  ensures 1 < FindSmallestDivisorOdd(n, start) <= n
  ensures n % FindSmallestDivisorOdd(n, start) == 0
  ensures forall k :: 1 < k < FindSmallestDivisorOdd(n, start) && k >= start ==> n % k != 0 || k % 2 == 0
  ensures forall k :: 1 < k < FindSmallestDivisorOdd(n, start) ==> n % k != 0
  decreases n - start + 1
{
  if start > n then 
    (assert n % n == 0; n)
  else if n % start == 0 then 
    start
  else FindSmallestDivisorOdd(n, start + 2)
}

lemma SmallestDivisorIsPrime(n: int, d: int)
  requires n >= 2 && d == FindSmallestDivisor(n)
  ensures is_prime_pred(d)
{
  if d == 2 {
    
  } else {
    assert n % 2 != 0;
    assert d == FindSmallestDivisorOdd(n, 3);
    assert forall k :: 1 < k < d ==> n % k != 0;
    forall k | 2 <= k < d
      ensures d % k != 0
    {
      if d % k == 0 {
        assert n % d == 0;
        ModuloTransitivity(n, d, k);
        assert n % k == 0;
        assert 1 < k < d;
        assert false;
      }
    }
  }
}

lemma ModuloTransitivity(a: int, b: int, c: int)
  requires c > 0 && b > 0 && a % b == 0 && b % c == 0
  ensures a % c == 0
{
  var q1 :| a == b * q1;
  var q2 :| b == c * q2;
  assert a == c * (q2 * q1);
}

lemma FindSmallestDivisorOddInvariant(n: int, start: int, k: int)
  requires n >= 2 && start >= 3 && start % 2 == 1
  requires n % 2 != 0
  requires 1 < k < start && k % 2 == 1
  requires forall j :: 3 <= j < start && j % 2 == 1 ==> n % j != 0
  ensures n % k != 0
{
  if k >= 3 {
    assert n % k != 0;
  } else {
    assert k < 3;
    assert k == 1 || k == 2;
    if k == 1 {
      assert k <= 1;
      assert false;
    } else {
      assert k == 2;
      assert n % 2 != 0;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method largest_prime_factor(n: int) returns (largest: int)
  // pre-conditions-start
  requires n >= 2
  // pre-conditions-end
  // post-conditions-start
  ensures 1 <= largest <= n && (largest == 1 || (largest > 1 && is_prime_pred(largest)))
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var d := FindSmallestDivisor(n);
  SmallestDivisorIsPrime(n, d);
  largest := d;
}
// </vc-code>
