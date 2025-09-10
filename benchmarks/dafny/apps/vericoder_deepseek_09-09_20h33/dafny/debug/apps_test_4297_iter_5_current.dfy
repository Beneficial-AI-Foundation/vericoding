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
lemma LCMLemma(a: int, b: int)
  requires a >= 1 && b >= 1
  ensures LCM(a, b) % a == 0 && LCM(a, b) % b == 0
{
  if a % b == 0 {
    // LCM is a, which is divisible by both a and b
  } else if b % a == 0 {
    // LCM is b, which is divisible by both a and b
  } else {
    // LCM is a*b, which is divisible by both a and b
    assert a * b % a == 0;
    assert a * b % b == 0;
  }
}

lemma IsSmallestLemma(result: int, n: int)
  requires n >= 1 && result % 2 == 0 && result % n == 0
  requires result == (if n % 2 == 0 then n else n * 2)
  ensures IsSmallest(result, n)
{
  if n % 2 == 0 {
    forall k: int | 1 <= k < result 
      ensures !(k % 2 == 0 && k % n == 0)
    {
      if k % 2 == 0 && k % n == 0 {
        // k is a positive multiple of n and k < n
        // But the smallest positive multiple of n is n itself
        assert n % n == 0 && (n % 2 == 0);
        assert k < n;
        // k cannot be a positive multiple of n that is less than n
        assert false;
      }
    }
  } else {
    forall k: int | 1 <= k < result 
      ensures !(k % 2 == 0 && k % n == 0)
    {
      if k % 2 == 0 && k % n == 0 {
        // k is a multiple of n and even, so k = m * n for some m >= 1
        // Since n is odd, m must be even for k to be even
        // The smallest even m is 2, giving k = 2n = result
        // But k < result, so no such k exists
        var m := k / n;
        assert k == m * n;
        assert m >= 1;
        assert m < 2;
        assert m == 1;
        assert k == n;
        // n is odd, but k is even - contradiction
        assert n % 2 != 0;
        assert k % 2 == 0;
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
  } else {
    result := n * 2;
  }
  
  assert result % 2 == 0;
  assert result % n == 0;
  
  IsSmallestLemma(result, n);
  assert IsSmallest(result, n);
}
// </vc-code>

