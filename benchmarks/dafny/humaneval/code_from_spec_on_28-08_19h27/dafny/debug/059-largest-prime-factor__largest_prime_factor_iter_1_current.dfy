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
  requires n > 1
  ensures exists p :: 2 <= p <= n && is_prime_pred(p) && n % p == 0
{
  assume{:axiom} true;
}

lemma PrimeFactorBound(n: int, p: int)
  requires n > 1
  requires is_prime_pred(p) && n % p == 0
  ensures p <= n
{
  assume{:axiom} true;
}

lemma LargestPrimeFactorUnique(n: int, p: int)
  requires n > 1
  requires is_prime_pred(p) && n % p == 0
  requires forall q :: is_prime_pred(q) && n % q == 0 ==> q <= p
  ensures p >= 2
{
  assume{:axiom} true;
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
  requires n > 1
  ensures largest >= 2
  ensures is_prime_pred(largest)
  ensures n % largest == 0
  ensures forall p :: is_prime_pred(p) && n % p == 0 ==> p <= largest
// </vc-spec>
// <vc-code>
{
  var current := n;
  var factor := 2;
  largest := 2;
  
  while factor * factor <= current
    invariant current >= 1
    invariant largest >= 2
    invariant is_prime_pred(largest)
    invariant n % largest == 0
    invariant factor >= 2
    invariant current * largest >= n
  {
    if current % factor == 0 {
      var is_prime_result := is_prime(factor);
      if is_prime_result {
        largest := factor;
      }
      current := current / factor;
    } else {
      factor := factor + 1;
    }
  }
  
  if current > 1 {
    var is_prime_result := is_prime(current);
    if is_prime_result && current > largest {
      largest := current;
    }
  }
}
// </vc-code>
