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
lemma ModSmallLemma(k:int, n:int)
  requires 0 <= k < n && n >= 1
  ensures k % n == k
{
  // Division algorithm
  assert k == n * (k / n) + k % n;
  // k % n is between 0 and n-1
  assert 0 <= k % n;
  assert k % n < n;
  // Hence n*(k/n) <= k < n
  assert n * (k / n) <= k;
  assert k < n;
  // If k / n >= 1 then n*(k/n) >= n, contradicting n*(k/n) <= k < n
  if k / n >= 1 {
    assert n * (k / n) >= n;
    assert n <= n * (k / n);
    assert n <= k; // from n <= n*(k/n) and n*(k/n) <= k
    assert false;
  }
  // So k / n < 1 and since k / n >= 0 we get k / n == 0
  assert 0 <= k / n;
  assert k / n < 1;
  assert k / n == 0;
  // therefore k == k % n
  assert k == k % n;
}

lemma NoSmallerWhenEven(n:int)
  requires n >= 1 && n % 2 == 0
  ensures forall k:int {:trigger k % n, k % 2} :: 1 <= k < n ==> !(k % 2 == 0 && k % n == 0)
{
  forall k | 1 <= k < n {
    if k % 2 == 0 && k % n == 0 {
      // k % n == 0 and 1 <= k < n implies contradiction via ModSmallLemma
      ModSmallLemma(k, n);
      assert k % n == k;
      // from k % n == 0 and k % n == k we get k == 0, contradicting 1 <= k
      assert k == 0;
      assert false;
    }
  }
}

lemma NoSmallerWhenOdd(n:int)
  requires n >= 1 && n % 2 != 0
  ensures forall k:int {:trigger k % n, k % 2} :: 1 <= k < 2 * n ==> !(k % 2 == 0 && k % n == 0)
{
  forall k | 1 <= k < 2 * n {
    if k % 2 == 0 && k % n == 0 {
      // If k < n then ModSmallLemma gives contradiction
      if k < n {
        ModSmallLemma(k, n);
        assert k % n == k;
        assert k == 0;
        assert false;
      } else {
        // So k >= n and k < 2n, hence 1 <= k/n < 2
        assert k >= n;
        assert k < 2 * n;
        // k is multiple of n so k/n is integer; from n <= k < 2n we get k/n == 1
        assert k / n >= 1;
        assert k / n < 2;
        assert k / n == 1;
        assert k == n;
        // n odd implies k odd, contradicting k % 2 == 0
        assert n % 2 != 0;
        assert k % 2 != 0;
        assert false;
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
    assert result == n;
    // basic facts
    assert result >= 1;
    assert result % n == 0;
    assert result % 2 == 0;
    // smallest property
    NoSmallerWhenEven(n);
    assert forall k:int :: 1 <= k < result ==> !(k % 2 == 0 && k % n == 0);
  } else {
    result := n * 2;
    assert result == 2 * n;
    // basic facts
    assert result >= 1;
    assert result % n == 0;
    assert result % 2 == 0;
    // smallest property
    NoSmallerWhenOdd(n);
    assert forall k:int :: 1 <= k < result ==> !(k % 2 == 0 && k % n == 0);
  }
}
// </vc-code>

