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
  
  // Find smallest divisor
  var sd := smallest_divisor(n);
  smallest_divisor_is_prime(n);
  assert 2 <= sd <= n;
  assert is_prime_pred(sd);
  assert n % sd == 0;
}

function smallest_divisor(m: int): int
  requires m >= 2
  ensures 2 <= smallest_divisor(m) <= m
  ensures m % smallest_divisor(m) == 0
  ensures forall k :: 2 <= k < smallest_divisor(m) ==> m % k != 0
{
  smallest_divisor_from(m, 2)
}

function smallest_divisor_from(m: int, start: int): int
  requires m >= 2
  requires 2 <= start <= m + 1
  requires forall k :: 2 <= k < start ==> m % k != 0
  decreases m - start + 1
  ensures 2 <= smallest_divisor_from(m, start) <= m
  ensures m % smallest_divisor_from(m, start) == 0
  ensures forall k :: 2 <= k < smallest_divisor_from(m, start) ==> m % k != 0
{
  if start > m then m
  else if m % start == 0 then start
  else smallest_divisor_from(m, start + 1)
}

lemma smallest_divisor_is_prime(m: int)
  requires m >= 2
  ensures is_prime_pred(smallest_divisor(m))
{
  var d := smallest_divisor(m);
  assert 2 <= d <= m;
  assert m % d == 0;
  assert forall k :: 2 <= k < d ==> m % k != 0;
  
  // Prove d is prime
  if !is_prime_pred(d) {
    // d has a divisor
    assert exists k :: 2 <= k < d && d % k == 0;
    var k :| 2 <= k < d && d % k == 0;
    
    // Since d divides m and k divides d, k divides m
    assert m % d == 0;
    assert d % k == 0;
    
    // m = d * q for some q
    var q := m / d;
    assert m == d * q;
    
    // d = k * r for some r  
    var r := d / k;
    assert d == k * r;
    
    // Therefore m = k * r * q
    assert m == k * r * q;
    assert m % k == 0;
    
    // But this contradicts that k < d and d is the smallest divisor
    assert k < d;
    assert forall j :: 2 <= j < d ==> m % j != 0;
    assert false;
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

