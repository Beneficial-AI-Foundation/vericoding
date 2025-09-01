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
  assert is_prime_pred(d);
}

function FindSmallestDivisor(n: int): int
  requires n >= 2
  ensures 1 < FindSmallestDivisor(n) <= n
  ensures n % FindSmallestDivisor(n) == 0
  ensures is_prime_pred(FindSmallestDivisor(n))
{
  if n % 2 == 0 then 2
  else FindSmallestOddDivisor(n, 3)
}

function FindSmallestOddDivisor(n: int, candidate: int): int
  requires n >= 3 && n % 2 != 0
  requires candidate >= 3 && candidate % 2 == 1
  requires candidate <= n
  ensures 1 < FindSmallestOddDivisor(n, candidate) <= n
  ensures n % FindSmallestOddDivisor(n, candidate) == 0
  ensures is_prime_pred(FindSmallestOddDivisor(n, candidate))
  decreases n - candidate
{
  if candidate == n then n
  else if n % candidate == 0 then candidate
  else FindSmallestOddDivisor(n, candidate + 2)
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
  var current := n;
  
  while current > 1
    invariant current >= 1
    invariant largest >= 1
    invariant largest == 1 || is_prime_pred(largest)
    decreases current
  {
    if current == 1 {
      break;
    }
    
    var factor := 2;
    while factor * factor <= current && current % factor != 0
      invariant factor >= 2
      invariant forall i :: 2 <= i < factor ==> current % i != 0
      decreases current - factor * factor
    {
      factor := factor + 1;
    }
    
    if factor * factor <= current {
      current := current / factor;
      if is_prime_pred(factor) && factor > largest {
        largest := factor;
      }
    } else {
      if is_prime_pred(current) && current > largest {
        largest := current;
      }
      current := 1;
    }
  }
  
  if largest == 1 {
    largest := n;
  }
}
// </vc-code>

