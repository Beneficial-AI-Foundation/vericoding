predicate ValidInput(n: int)
{
    n >= 1
}

predicate DivisibleByBoth(result: int, n: int)
    requires n >= 1
{
    result % 2 == 0 && result % n == 0
}

predicate IsSmallest(result: int, n: int)
    requires n >= 1
{
    forall k: int :: 1 <= k < result ==> !(k % 2 == 0 && k % n == 0)
}

function LCM(a: int, b: int): int
    requires a >= 1 && b >= 1
{
    if a % b == 0 then a
    else if b % a == 0 then b
    else a * b
}

// <vc-helpers>
lemma lemma_isSmallest_for_even_n(n: int)
  requires n >= 1
  requires n % 2 == 0
  ensures IsSmallest(n, n)
{
  forall k: int | 1 <= k < n
    ensures !(k % 2 == 0 && k % n == 0)
  {
    if (k % 2 == 0 && k % n == 0) {
      assert k % n == 0; // k is a multiple of n
      // If k is a multiple of n and 1 <= k < n, this is a contradiction
      // because the smallest positive multiple of n is n itself.
      // Therefore, k must be at least n if it's a positive multiple of n.
      var m := k / n; // m must be an integer since k is a multiple of n
      assert k == m * n;
      // Since 1 <= k < n and n >= 1:
      // If m is an integer, and m*n is positive, m must be positive.
      assert m >= 1;
      // Also, k < n implies m*n < n. Since n >= 1, we can divide by n safely:
      assert m < 1;
      // This is a contradiction, as m must be an integer and cannot be both >= 1 and < 1.
      assert false; // This path should be unreachable
    }
  }
}

lemma lemma_isSmallest_for_odd_n(n: int)
  requires n >= 1
  requires n % 2 != 0
  ensures IsSmallest(n * 2, n)
{
  assert (n * 2) % 2 == 0;
  assert (n * 2) % n == 0;

  forall k: int | 1 <= k < n * 2
    ensures !(k % 2 == 0 && k % n == 0)
  {
    if (k % 2 == 0 && k % n == 0) {
      // k is a multiple of n, so k = m * n for some integer m >= 1
      assert k % n == 0;
      var m := k / n;
      assert k == m * n;
      assert m >= 1; // Since k >= 1 and n >= 1

      // We also know k < n * 2.
      // So, m * n < n * 2. Since n >= 1, we can divide by n safely.
      assert (m * n) < (2 * n);
      assert m < 2;

      // Combining m >= 1 and m < 2, we conclude m must be 1.
      assert m == 1; // This means k == n.

      // Now substitute k = n into k % 2 == 0.
      // So, n % 2 == 0.
      assert n % 2 == 0;

      // This contradicts the premise n % 2 != 0.
      assert false; // Contradiction
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result >= 1
    ensures DivisibleByBoth(result, n)
    ensures IsSmallest(result, n)
    ensures (n % 2 == 0 ==> result == n) && (n % 2 != 0 ==> result == n * 2)
// </vc-spec>
// <vc-code>
{
    if n % 2 == 0 {
        result := n;
        lemma_isSmallest_for_even_n(n);
        assert n % 2 == 0; // property for the conditional branch
        assert DivisibleByBoth(result, n); // n % 2 == 0 and n % n == 0 are true
    } else {
        result := n * 2;
        lemma_isSmallest_for_odd_n(n);
        assert n % 2 != 0; // property for the conditional branch
        assert DivisibleByBoth(result, n); // (n*2) % 2 == 0 and (n*2) % n == 0 are true
    }
    assert result >= 1; // Since n >= 1, n or n*2 is also >= 1
}
// </vc-code>

