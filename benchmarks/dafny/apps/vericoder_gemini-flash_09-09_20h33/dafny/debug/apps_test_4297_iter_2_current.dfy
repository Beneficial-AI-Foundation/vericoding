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
      assert k % n == 0;
      // If k % n == 0 and k < n and k >= 1, then k can't be a multiple of n
      // unless n is 0 or less, which is ruled out by n >= 1.
      assert k < n;
      assert k >= n; // This is the contradiction
      // Therefore, the assumption (k % 2 == 0 && k % n == 0) must be false.
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
    } else {
        result := n * 2;
        lemma_isSmallest_for_odd_n(n);
    }
    assert result >= 1; // Since n >= 1, n*2 is also >= 1
    assert DivisibleByBoth(result, n);
    assert IsSmallest(result, n);
    assert (n % 2 == 0 ==> result == n) && (n % 2 != 0 ==> result == n * 2);
}
// </vc-code>

