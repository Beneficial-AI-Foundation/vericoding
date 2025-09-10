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
  }
}

lemma IsSmallestLemma(result: int, n: int)
  requires n >= 1 && result % 2 == 0 && result % n == 0
  requires result == (if n % 2 == 0 then n else n * 2)
  ensures IsSmallest(result, n)
{
  if n % 2 == 0 {
    // n is even, result = n
    // Show that no smaller positive integer is divisible by both 2 and n
    forall k: int | 1 <= k < result 
      ensures !(k % 2 == 0 && k % n == 0)
    {
      if k % 2 == 0 {
        // k is even, check if divisible by n
        // Since n is the result and k < result, k cannot be divisible by n
        // because n > k (unless k >= n, which contradicts k < result = n)
      }
    }
  } else {
    // n is odd, result = 2n
    // Show that no smaller positive integer is divisible by both 2 and n
    forall k: int | 1 <= k < result 
      ensures !(k % 2 == 0 && k % n == 0)
    {
      if k % 2 == 0 && k % n == 0 {
        // k is a common multiple, so k = m * n where m >= 1
        var m := k / n;
        assert k == m * n;
        // Since k is even and n is odd, m must be even
        // The smallest even m is 2, giving k = 2n, but k < result = 2n
        // Contradiction: cannot have m < 2 since 0 < m < 2 and integer means m = 1
        // but m = 1 gives k = n, which is odd (contradicts k being even)
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
  
  // Prove the postconditions
  assert result % 2 == 0;
  assert result % n == 0;
  
  // Call the lemma to establish IsSmallest
  IsSmallestLemma(result, n);
}
// </vc-code>

