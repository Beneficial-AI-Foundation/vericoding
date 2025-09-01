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
function IsPrime(k: int): bool
  requires k >= 2 // Primality is defined for k >= 2
{
  forall i :: 2 <= i < k ==> (k % i != 0)
}

predicate IsFactor(f: int, n: int)
  requires n >= 1
  requires f >= 1
{
  n % f == 0
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
  var current_n := n;
  var largest_found := 1;
  var d := 2;

  while d * d <= current_n
    invariant 2 <= d
    invariant current_n >= 1
    invariant largest_found >= 1
    invariant largest_found == 1 || (largest_found >= 2 && IsPrime(largest_found))
    invariant n % current_n == 0
    invariant forall k :: (k >= 2 && IsPrime(k) && IsFactor(k, n / current_n)) ==> k <= largest_found
    invariant forall k :: (k >= 2 && k < d && IsPrime(k) && IsFactor(k, n)) ==> !IsFactor(k, current_n)
    invariant forall k :: (k >= 2 && k < d && IsPrime(k)) ==> current_n % k != 0
    decreases current_n
  {
    if current_n % d == 0 {
      largest_found := d;
      current_n := current_n / d;
    } else {
      d := d + 1;
    }
  }

  if current_n > 1 {
    largest_found := current_n;
  }

  largest := largest_found;
  assert largest >= 1;
  if largest > 1 {
    assert IsPrime(largest) by {
      if largest == n {
        assert d*d > current_n;
        assert d*d > largest;
        forall k | 2 <= k < largest ensures largest % k != 0 {
          if largest % k == 0 {
            assert !IsFactor(k, current_n) by {
              assert k < d;
              assert (forall l :: (l >= 2 && l < k && IsPrime(l)) ==> current_n % l != 0); // From the invariant applied to k
              assert IsPrime(k); // From the quantifer
              if k < d { // This branch handles the case required by the proof
                 assert (forall m :: (m >= 2 && m < d && IsPrime(m)) ==> current_n % m != 0); // From loop invariant `forall k_inv :: (k_inv >= 2 && k_inv < d && IsPrime(k_inv)) ==> current_n % k_inv != 0` substituting `k_inv` with `m`
                 if current_n % k == 0 { // For this to be true, the invariant implies that `k` must be greater than or equal to `d`, but `k < d` is assumed. Thus, a contradiction.
                    assert k >= d; // This would contradict k < d;
                    assert false;
                 }
              }
            }
             assert false;
          }
        }
      } else if largest == current_n {
        assert d*d > current_n;
        forall k | 2 <= k < largest ensures largest % k != 0 {
          if largest % k == 0 {
             assert !IsFactor(k, current_n) by {
               assert k < d;
               assert IsPrime(k);
               if k < d {
                 assert (forall m :: (m >= 2 && m < d && IsPrime(m)) ==> current_n % m != 0);
                 if current_n % k == 0 {
                    assert k >= d;
                    assert false;
                 }
               }
             }
             assert false;
          }
        }
      } else { // largest was largest_found before the current_n > 1 check, not current_n
        assert IsPrime(largest); // Already proven by an invariant
      }
    }
  }
}
// </vc-code>

