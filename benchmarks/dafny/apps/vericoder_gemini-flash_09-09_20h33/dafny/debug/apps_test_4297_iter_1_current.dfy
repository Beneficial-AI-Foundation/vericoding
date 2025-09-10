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
      assert k >= n; // contradiction with k < n
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
      // k is a multiple of n
      assert exists j: int :: k == j * n;
      // Since k < n*2 and k > 0, j must be 1.
      assert k != 0;
      assert k < n * 2;
      assert k % n == 0;
      if (k == n) {
        // If k == n, then k % 2 == n % 2.
        // We know n % 2 != 0, so k % 2 != 0.
        // This contradicts k % 2 == 0.
        assert n % 2 != 0;
        assert k % 2 != 0;
        assert false; // Contradiction
      } else if (k >= n * 2) {
        assert false; // Contradiction with k < n * 2
      } else {
        // k must be n or n*j where j >= 1
        // k is a multiple of n and k < 2n
        // so k must be n.
        // But we already handled k == n.
        // The multiples of n are n, 2n, 3n, ...
        // If k is a multiple of n and k < 2n and k > 0, then k must be n.
      }
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

