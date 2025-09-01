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
lemma prime_factor_exists(n: int)
  requires n >= 2
  ensures exists p :: 2 <= p <= n && is_prime_pred(p) && n % p == 0
{
  if is_prime_pred(n) {
    // n itself is prime
    assert n % n == 0;
    return;
  }
  
  // n is not prime, so it has a divisor
  assert exists d :: 2 <= d < n && n % d == 0;
  var d :| 2 <= d < n && n % d == 0;
  
  // Find the smallest divisor
  var smallest := 2;
  while smallest <= d
    invariant 2 <= smallest <= d + 1
    invariant forall j :: 2 <= j < smallest ==> n % j != 0
  {
    if n % smallest == 0 {
      break;
    }
    smallest := smallest + 1;
  }
  
  assert n % smallest == 0;
  
  // Prove that smallest is prime
  forall k | 2 <= k < smallest
    ensures smallest % k != 0
  {
    if smallest % k == 0 {
      // k divides smallest and smallest divides n, so k divides n
      // We need to prove n % k == 0
      var q1 := smallest / k;
      assert smallest == k * q1;
      var q2 := n / smallest;
      assert n == smallest * q2;
      assert n == k * q1 * q2;
      assert n % k == 0;
      assert false; // Contradiction with loop invariant
    }
  }
  
  assert is_prime_pred(smallest);
  assert n % smallest == 0;
  assert 2 <= smallest <= n;
}

function smallest_divisor(m: int): int
  requires m >= 2
  ensures 2 <= smallest_divisor(m) <= m
  ensures m % smallest_divisor(m) == 0
{
  if m % 2 == 0 then 2
  else if m % 3 == 0 then 3
  else smallest_divisor_from(m, 5)
}

function smallest_divisor_from(m: int, start: int): int
  requires m >= 2
  requires start >= 2
  requires forall k :: 2 <= k < start ==> m % k != 0
  decreases m - start + 1
  ensures 2 <= smallest_divisor_from(m, start) <= m
  ensures m % smallest_divisor_from(m, start) == 0
{
  if start > m then m
  else if m % start == 0 then start
  else smallest_divisor_from(m, start + 1)
}

function smallest_prime_factor_of(m: int): int
  requires m >= 2
  ensures 2 <= smallest_prime_factor_of(m) <= m
  ensures is_prime_pred(smallest_prime_factor_of(m))
  ensures m % smallest_prime_factor_of(m) == 0
{
  var d := smallest_divisor(m);
  assert forall k :: 2 <= k < d ==> m % k != 0;
  assert is_prime_pred(d) by {
    forall k | 2 <= k < d
      ensures d % k != 0
    {
      if d % k == 0 {
        assert k < d;
        assert 2 <= k;
        assert m % d == 0;
        var q := m / d;
        var r := d / k;
        assert d == k * r;
        assert m == d * q == k * r * q;
        assert m % k == 0;
        assert false;
      }
    }
  }
  d
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
  largest := 1;
  var i := 2;
  
  while i <= n
    invariant 2 <= i <= n + 1
    invariant 1 <= largest <= n
    invariant largest == 1 || (largest > 1 && is_prime_pred(largest))
    invariant forall p :: 2 <= p < i && is_prime_pred(p) && n % p == 0 ==> p <= largest
  {
    if n % i == 0 {
      var prime := is_prime(i);
      if prime {
        largest := i;
      }
    }
    i := i + 1;
  }
  
  if largest == 1 {
    prime_factor_exists(n);
    assert false;
  }
}
// </vc-code>

