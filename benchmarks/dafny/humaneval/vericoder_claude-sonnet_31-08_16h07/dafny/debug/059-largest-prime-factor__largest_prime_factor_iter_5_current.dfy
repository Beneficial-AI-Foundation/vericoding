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

lemma SmallestDivisorIsPrime(n: int, d: int)
  requires n >= 2
  requires 1 < d <= n
  requires n % d == 0
  requires forall i :: 2 <= i < d ==> n % i != 0
  ensures is_prime_pred(d)
{
  forall i | 2 <= i < d
    ensures d % i != 0
  {
    if d % i == 0 {
      assert n % i == 0;
      assert false;
    }
  }
}

lemma PrimalityLemma(p: int)
  requires p >= 2
  requires forall i :: 2 <= i < p ==> p % i != 0
  ensures is_prime_pred(p)
{
}

lemma LargePrimeLemma(current: int, candidate: int)
  requires current > 1
  requires candidate >= 3
  requires candidate * candidate > current
  requires forall i :: 2 <= i < current ==> current % i != 0
  ensures is_prime_pred(current)
{
  forall i | 2 <= i < current
    ensures current % i != 0
  {
    if current % i == 0 {
      assert false;
    }
  }
}

lemma CurrentPrimalityHelper(current: int, candidate: int)
  requires current > 1
  requires candidate >= 3
  requires candidate * candidate > current
  ensures forall i :: 2 <= i < current ==> current % i != 0
{
  forall i | 2 <= i < current
    ensures current % i != 0
  {
    if current % i == 0 {
      if i == 1 {
        assert false;
      } else if i >= candidate {
        if i * i <= current {
          assert i < candidate;
          assert false;
        }
      }
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
  if n == 2 {
    largest := 2;
    return;
  }
  
  largest := 1;
  var current := n;
  
  if current % 2 == 0 {
    largest := 2;
    while current % 2 == 0
      invariant current >= 1
      decreases current
    {
      current := current / 2;
    }
  }
  
  var candidate := 3;
  while candidate * candidate <= current
    invariant current >= 1
    invariant largest >= 1
    invariant candidate >= 3
    invariant candidate % 2 == 1
    invariant largest <= n
    invariant largest == 1 || is_prime_pred(largest)
    decreases current - candidate + 1
  {
    if current % candidate == 0 {
      largest := candidate;
      PrimalityLemma(candidate);
      while current % candidate == 0
        invariant current >= 1
        decreases current
      {
        current := current / candidate;
      }
    }
    candidate := candidate + 2;
  }
  
  if current > 1 {
    CurrentPrimalityHelper(current, candidate);
    LargePrimeLemma(current, candidate);
    largest := current;
  }
}
// </vc-code>

