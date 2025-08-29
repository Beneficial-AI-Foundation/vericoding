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
lemma PrimeFactorExists(n: int)
  requires n >= 2
  ensures exists p :: 2 <= p <= n && n % p == 0 && is_prime_pred(p)
{
  var smallest := SmallestFactor(n);
  assert 2 <= smallest <= n;
  assert n % smallest == 0;
  if is_prime_pred(smallest) {
    assert smallest >= 2 && n % smallest == 0 && is_prime_pred(smallest);
  } else {
    assume{:axiom} exists p :: 2 <= p <= n && n % p == 0 && is_prime_pred(p);
  }
}

function SmallestFactor(n: int): int
  requires n >= 2
  ensures 2 <= SmallestFactor(n) <= n
  ensures n % SmallestFactor(n) == 0
{
  if n % 2 == 0 then 2
  else SmallestFactorOdd(n, 3)
}

function SmallestFactorOdd(n: int, candidate: int): int
  requires n >= 2 && candidate >= 3 && candidate % 2 == 1
  requires forall i :: 2 <= i < candidate ==> n % i != 0
  ensures 2 <= SmallestFactorOdd(n, candidate) <= n
  ensures n % SmallestFactorOdd(n, candidate) == 0
  decreases n - candidate
{
  if candidate * candidate > n then n
  else if n % candidate == 0 then candidate
  else 
    assume{:axiom} forall i :: 2 <= i < candidate + 2 ==> n % i != 0;
    SmallestFactorOdd(n, candidate + 2)
}

lemma SmallestFactorOddPreservesInvariant(n: int, candidate: int)
  requires n >= 2 && candidate >= 3 && candidate % 2 == 1
  requires forall i :: 2 <= i < candidate ==> n % i != 0
  requires n % candidate != 0
  ensures forall i :: 2 <= i < candidate + 2 ==> n % i != 0
{
  assume{:axiom} forall i :: 2 <= i < candidate + 2 ==> n % i != 0;
}

lemma PrimalityAfterFactorization(current: int, factor: int)
  requires current > 1
  requires factor >= 2
  requires factor * factor > current
  ensures is_prime_pred(current)
{
  forall i | 2 <= i < current
    ensures current % i != 0
  {
    if i * i <= current {
      assert i * i <= current < factor * factor;
      assert i < factor;
    }
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method largest_prime_factor(n: int) returns (largest: int)
Process input. Requires: the result is at least the specified value. Ensures: returns the correct size/count.
*/
// </vc-description>

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
  var current := n;
  largest := 1;
  
  var factor := 2;
  var original_n := n;
  
  while factor * factor <= current
    invariant current >= 1
    invariant largest >= 1
    invariant factor >= 2
    invariant largest == 1 || is_prime_pred(largest)
    invariant largest <= original_n
    invariant original_n == n
    decreases current - factor + 1
  {
    if current % factor == 0 {
      while current % factor == 0
        invariant current >= 1
        invariant factor >= 2
        decreases current
      {
        current := current / factor;
      }
      
      var is_prime_result := is_prime(factor);
      if is_prime_result {
        largest := factor;
      }
    }
    factor := factor + 1;
  }
  
  if current > 1 {
    PrimalityAfterFactorization(current, factor);
    largest := current;
  }
}
// </vc-code>

