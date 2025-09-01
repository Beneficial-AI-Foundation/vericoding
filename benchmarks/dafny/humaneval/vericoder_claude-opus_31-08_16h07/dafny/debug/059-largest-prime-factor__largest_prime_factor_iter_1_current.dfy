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
  var i := 2;
  while i <= n
    invariant 2 <= i <= n + 1
    invariant forall j :: 2 <= j < i && is_prime_pred(j) ==> n % j != 0
  {
    if n % i == 0 && is_prime_pred(i) {
      return;
    }
    i := i + 1;
  }
  
  // If no prime factor found yet, n itself must be prime
  assert forall j :: 2 <= j < n && is_prime_pred(j) ==> n % j != 0;
  
  // Prove n is prime
  forall k | 2 <= k < n
    ensures n % k != 0
  {
    if n % k == 0 {
      // k divides n, so k has a prime factor that also divides n
      var p := smallest_prime_factor_of(k);
      assert 2 <= p <= k < n;
      assert is_prime_pred(p);
      assert k % p == 0;
      assert n % p == 0;
      assert false;
    }
  }
  assert is_prime_pred(n);
  assert n % n == 0;
}

function smallest_prime_factor_of(m: int): int
  requires m >= 2
  ensures 2 <= smallest_prime_factor_of(m) <= m
  ensures is_prime_pred(smallest_prime_factor_of(m))
  ensures m % smallest_prime_factor_of(m) == 0
{
  if is_prime_pred(m) then m
  else 
    var d :| 2 <= d < m && m % d == 0;
    smallest_prime_factor_of(d)
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

