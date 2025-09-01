

// <vc-helpers>
lemma lemma_i_le_k_or_prime(k: int, i: int)
  requires 2 <= i
  requires i*i > k
  requires forall j :: 2 <= j < i ==> k % j != 0
  ensures forall x :: 2 <= x < k ==> k % x != 0
{
  if i > k
  {
      forall x | 2 <= x < k
      {
          assert x < i;
          assert k%x != 0;
      }
  } else {
    // If i <= k, then k is not divisible by any number less than i.
    // Since i*i > k and i is the smallest number for which k % i == 0
    // would mean k is composite, it implies k is prime.
    // The invariant in the calling loop ensures k is not divisible by any j < i.
    // This lemma completes the proof by showing that if no divisors are found up to sqrt(k),
    // then no divisors exist between sqrt(k) and k.
    forall x | 2 <= x < k
      ensures k % x != 0
    {
      if x < i {
        assert k % x != 0;
      } else if x >= i {
        // Since i * i > k, if x >= i, then x * x > k too.
        // If x is a divisor of k, then k/x is also a divisor.
        // And k/x < k/i.
        // We know k/x cannot be less than 2.
        assert k % x != 0 by {
          if k % x == 0 {
            var y := k / x;
            assert 1 <= y < i; // Since x >= i and x is a divisor, y must be < i.
            // If k % y == 0, and y is less than i, but y is also a divisor of k.
            // This contradicts the premise (forall j :: 2 <= j < i ==> k % j != 0) unless y = 1.
            // If y = 1, then x = k. But x < k, which is a contradiction.
            // So y must be >= 2.
            assert y >= 2;
            assert k % y == 0;
            // This contradicts the premise (forall j :: 2 <= j < i ==> k % j != 0)
            // since we established y is a divisor of k, and 2 <= y < i.
            // Thus, k % x != 0.
          }
        }
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method is_prime(k: int) returns (result: bool)
  // pre-conditions-start
  requires k >= 2
  // pre-conditions-end
  // post-conditions-start
  ensures result ==> forall i :: 2 <= i < k ==> k % i != 0
  ensures !result ==> exists j :: 2 <= j < k && k % j == 0
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if k == 2 then return true;
  if k % 2 == 0 then return false;
  var i := 3;
  while i * i <= k
    invariant 2 <= i <= k + 1
    invariant i % 2 == 1 // i is always odd
    invariant forall j :: 2 <= j < i ==> k % j != 0
  {
    if k % i == 0 then
      return false;
    i := i + 2;
  }
  lemma_i_le_k_or_prime(k, i);
  return true;
}
// </vc-code>

